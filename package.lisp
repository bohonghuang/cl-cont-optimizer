(defpackage cl-cont-optimizer
  (:use #:cl #:alexandria #:trivial-macroexpand-all)
  (:export #:with-cont-optimizer #:*allow-multiple-value-p*))

(in-package #:cl-cont-optimizer)

(defvar +without-call/cc-mark+ (gensym "WITHOUT-CALL/CC"))

(defvar *subform-has-call/cc-p* nil)

(defvar *lexcial-tags* nil)

(defvar *lexcial-functions* nil)

(defvar *lexcial-blocks* nil)

(defvar *top-level-optimizer-p* t)

(defparameter *allow-multiple-value-p* t)

(defmacro with-propagated-subform-call/cc-p (&body body)
  (with-gensyms (pred)
    `(let ((,pred nil))
       (multiple-value-prog1
           (let ((*subform-has-call/cc-p* nil))
             (multiple-value-prog1 (progn . ,body)
               (setf ,pred *subform-has-call/cc-p*)))
         (unless *subform-has-call/cc-p*
           (setf *subform-has-call/cc-p* ,pred))))))

(defmacro with-protected-subform-call/cc-p (&body body)
  `(let ((*subform-has-call/cc-p* nil)) . ,body))

(defun conditional-call/cc (form)
  (if *subform-has-call/cc-p*
      `(cont:with-call/cc ,form)
      `(cont:without-call/cc ,form)))

(defmacro without-call/cc-with-mark (&body body)
  (if *allow-multiple-value-p*
      `(cont:without-call/cc ,+without-call/cc-mark+ . ,body)
      `(cont:without-call/cc . ,body)))

(defun optimize-body (forms)
  (loop :with group :and terminator := (gensym)
        :for (form next) :on (nconc forms (list terminator))
        :if (and (listp form) (eq (car form) 'cont:without-call/cc))
          :do (push (cdr form) group)
        :else
          :when group
            :collect `(without-call/cc-with-mark . ,(reduce #'nconc (nreverse group))) :into groups
            :and :do (setf group nil)
          :end :and
          :if (eql form terminator)
            :return groups
          :else
            :collect form :into groups))

(defun walk (form &optional env)
  (loop :while (or (and (listp form) (not (member (car form) '(cont:with-call/cc cont:without-call/cc lambda))))
                   (not (listp form)))
        :while (multiple-value-bind (expanded expandedp) (macroexpand-1 form env)
                 (when expandedp (setf form expanded))))
  (typecase form
    (cons
     (when (and (listp (car form)) (eq (caar form) 'lambda))
       (return-from walk (walk `(funcall . ,form) env)))
     (destructuring-case form
       ((the value-type form) `(the ,value-type ,(walk form env)))
       (((declare declaim proclaim quote) &rest args) (declare (ignore args)) form)
       ((locally &rest body) `(locally . ,(optimize-body body)))
       (((let let*) bindings &rest body)
        (with-propagated-subform-call/cc-p
          (conditional-call/cc
           (let ((bindings (loop :for binding :in bindings
                                 :if (listp binding)
                                   :collect `(,(first binding) ,(walk (second binding) env))
                                 :else
                                   :collect `(,binding nil)))
                 (bindings-have-call/cc-p *subform-has-call/cc-p*)
                 (body (optimize-body (mapcar (rcurry #'walk env) body))))
             (if (and *allow-multiple-value-p* *subform-has-call/cc-p*
                      (eq (car form) 'let) (> (length bindings) 1)
                      (not bindings-have-call/cc-p))
                 `(multiple-value-bind ,(mapcar #'first bindings)
                      (without-call/cc-with-mark (values . ,(mapcar #'second bindings)))
                    (locally . ,body))
                 `(,(car form) ,bindings . ,body))))))
       ((function name)
        (with-propagated-subform-call/cc-p
          (cond
            ((assoc-value *lexcial-functions* name)
             (setf *subform-has-call/cc-p* t) `(function ,name))
            ((and (listp name) (eq (car name) 'lambda)) (walk name env))
            (t `(function ,name)))))
       ((block name &rest body)
        (with-propagated-subform-call/cc-p
          (mapc (rcurry #'walk env) body)
          (conditional-call/cc
           `(block ,name . ,(let ((*lexcial-blocks* (acons name *subform-has-call/cc-p* *lexcial-blocks*)))
                              (optimize-body (mapcar (rcurry #'walk env) body)))))))
       ((return-from name result)
        (with-propagated-subform-call/cc-p
          (when (assoc-value *lexcial-blocks* name)
            (setf *subform-has-call/cc-p* t))
          (conditional-call/cc `(return-from ,name ,(walk result env)))))
       (((flet labels) definitions &rest body)
        (with-propagated-subform-call/cc-p
          (let ((functions (loop :for (name args . body) :in definitions
                                 :do (mapc (rcurry #'walk env) body)
                                 :collect name)))
            (conditional-call/cc
             `(,(car form)
               ,(loop :with *lexcial-functions* := (nconc (mapcar (rcurry
                                                                   #'cons
                                                                   (and (eq (car form) 'labels)
                                                                        *subform-has-call/cc-p*))
                                                                  functions)
                                                          *lexcial-functions*)
                      :for (name args . body) :in definitions
                      :collect `(,name ,args . ,(optimize-body (mapcar (rcurry #'walk env) body))))
               ,@(let ((*lexcial-functions* (nconc (mapcar (rcurry #'cons *subform-has-call/cc-p*) functions) *lexcial-functions*)))
                   (mapcar (rcurry #'walk env) body)))))))
       (((macrolet symbol-macrolet) definitions &rest body)
        `(,(car form) ,definitions (%with-cont-optimizer (,*lexcial-tags* ,*lexcial-functions* ,*lexcial-blocks*) . ,body)))
       ((multiple-value-call function &rest args)
        (with-propagated-subform-call/cc-p
          (conditional-call/cc
           `(multiple-value-call ,(walk function env) . ,(mapcar (rcurry #'walk env) args)))))
       ((cont:with-call/cc &rest body)
        (with-propagated-subform-call/cc-p
          (conditional-call/cc
           `(progn . ,(optimize-body (mapcar (rcurry #'walk env) body))))))
       ((cont:without-call/cc &rest body) (declare (ignore body)) form)
       ((tagbody &rest body)
        (let ((tags (loop :for form :in body
                          :when (symbolp form)
                            :collect form)))
          (with-propagated-subform-call/cc-p
            (mapc (rcurry #'walk env) body)
            (let ((*lexcial-tags* (nconc (mapcar (rcurry #'cons *subform-has-call/cc-p*) tags) *lexcial-tags*)))
              (conditional-call/cc `(tagbody . ,(remove-if #'null (optimize-body (mapcar (rcurry #'walk env) body)))))))))
       ((go tag)
        (with-propagated-subform-call/cc-p
          (when (assoc-value *lexcial-tags* tag)
            (setf *subform-has-call/cc-p* t))
          (conditional-call/cc form)))
       ((lambda args &rest body)
        (with-protected-subform-call/cc-p
          (conditional-call/cc
           `(lambda ,args . ,(optimize-body (mapcar (rcurry #'walk env) body))))))
       ((cont:call/cc function)
        (setf *subform-has-call/cc-p* t)
        `(cont:call/cc ,(walk function env)))
       ((progn &rest args)
        (with-propagated-subform-call/cc-p
          (conditional-call/cc
           `(progn . ,(optimize-body (mapcar (rcurry #'walk env) args))))))
       ((t &rest args)
        (with-propagated-subform-call/cc-p
          (when (assoc-value *lexcial-functions* (car form))
            (setf *subform-has-call/cc-p* t))
          (conditional-call/cc
           `(,(car form) . ,(mapcar (rcurry #'walk env) args)))))))
    (t form)))

(defmacro %with-cont-optimizer ((tags functions blocks) &body body &environment env &aux (*subform-has-call/cc-p* nil))
  (if *top-level-optimizer-p*
      (let ((*top-level-optimizer-p* nil)
            (*lexcial-tags* tags)
            (*lexcial-functions* functions)
            (*lexcial-blocks* blocks))
        `(cont:with-call/cc . ,(mapcar (rcurry #'walk env) body)))
      `(progn . ,body)))

(defun funcall-to-multiple-value-call (form)
  (typecase form
    ((and proper-list cons)
     (destructuring-case form
       ((funcall function &rest args)
        (if (and (= (length args) 1)
                 (listp (car args))
                 (eq (caar args) 'progn)
                 (eql (cadar args) +without-call/cc-mark+))
            `(multiple-value-call . ,(mapcar #'funcall-to-multiple-value-call (cons function args)))
            `(funcall . ,(mapcar #'funcall-to-multiple-value-call (cons function args)))))
       ((t &rest args) (declare (ignore args))
        (mapcar #'funcall-to-multiple-value-call form))))
    (t form)))

(defmacro with-cont-optimizer (&body body &environment env)
  (if *top-level-optimizer-p*
      (progn
        (when *allow-multiple-value-p*
          (multiple-value-bind (form supportp)
              (macroexpand-all `(%with-cont-optimizer (nil nil nil) . ,body) #-ecl env)
            (if supportp
                (setf body `(symbol-macrolet ((,+without-call/cc-mark+ nil))
                              ,(funcall-to-multiple-value-call form)))
                (setf *allow-multiple-value-p* nil))))
        (unless *allow-multiple-value-p*
          (setf body `(%with-cont-optimizer (nil nil nil) . ,body))))
      (setf body `(progn . ,body)))
  (values body))
