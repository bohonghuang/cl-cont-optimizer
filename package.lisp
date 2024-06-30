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

(defun conditional-call/cc (form &optional (unexpanded-form form))
  (if *subform-has-call/cc-p*
      `(cont:with-call/cc ,form)
      `(cont:without-call/cc ,(if (eq form unexpanded-form)
                                  unexpanded-form
                                  (block form
                                    (subst-if 'nil
                                              (lambda (atom)
                                                (when (eq atom 'cont:with-call/cc)
                                                  (return-from form form)))
                                              form)
                                    unexpanded-form)))))

(defmacro without-call/cc-with-mark (&body body)
  (if *allow-multiple-value-p*
      `(cont:without-call/cc ,+without-call/cc-mark+ . ,body)
      `(cont:without-call/cc . ,body)))

(defun optimize-body (forms)
  (loop :with group :and terminator := (gensym)
        :for (form next) :on (append forms (list terminator))
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

(defun propagate-funcall-function-has-call/cc-p (function)
  (when (and (listp function) (eq (car function) 'cont:with-call/cc))
    (setf *subform-has-call/cc-p* t))
  function)

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
       ((locally &rest body)
        (with-propagated-subform-call/cc-p
          (conditional-call/cc
           `(locally . ,(optimize-body (mapcar (rcurry #'walk env) body))))))
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
          (macrolet ((with-lexical-blocks (&body body)
                       `(let ((*lexcial-blocks* (acons name *subform-has-call/cc-p* *lexcial-blocks*)))
                          ,@body)))
            (with-lexical-blocks (mapc (rcurry #'walk env) body))
            (conditional-call/cc
             `(block ,name . ,(with-lexical-blocks (optimize-body (mapcar (rcurry #'walk env) body))))))))
       ((return-from name &optional result)
        (with-propagated-subform-call/cc-p
          (when (assoc-value *lexcial-blocks* name)
            (setf *subform-has-call/cc-p* t))
          (conditional-call/cc `(return-from ,name ,(with-propagated-subform-call/cc-p
                                                      (let ((form (walk result env)))
                                                        (if *subform-has-call/cc-p* form `(without-call/cc-with-mark ,form))))))))
       (((flet labels) definitions &rest body)
        (with-propagated-subform-call/cc-p
          (let ((functions (loop :for (name args . body) :in definitions
                                 :do (mapc (rcurry #'walk env) body)
                                 :collect name)))
            (conditional-call/cc
             `(,(car form)
               ,(loop :with *lexcial-functions* := (nconc (mapcar (rcurry #'cons (eq (car form) 'labels)) functions) *lexcial-functions*)
                      :for (name args . body) :in definitions
                      :collect `(,name ,args . ,(optimize-body (mapcar (rcurry #'walk env) body))))
               ,@(progn
                   (mapc (rcurry #'walk env) body)
                   (let ((*lexcial-functions* (nconc (mapcar (rcurry #'cons *subform-has-call/cc-p*) functions) *lexcial-functions*)))
                     (mapcar (rcurry #'walk env) body))))))))
       (((macrolet symbol-macrolet) definitions &rest body)
        (multiple-value-bind (expanded supportp environmentp)
            (ignore-errors (macroexpand-all `(,(car form) ,definitions (%%with-cont-optimizer (locally . ,body))) env))
          (declare (ignore expanded))
          (unless supportp
            (setf *subform-has-call/cc-p* t)
            (warn "CL-CONT-OPTIMIZER cannot optimize ~A because current implementation does not support ~A." (car form) 'macroexpand-all))
          (unless environmentp
            (warn "Current implementation does not support the ENVIRONMENT parameter of ~A, therefore CL-CONT-OPTIMIZER may not produce accurate optimization results for ~A." 'macroexpand-all (car form))))
        `(,(car form) ,definitions (%with-cont-optimizer (,*lexcial-tags* ,*lexcial-functions* ,*lexcial-blocks*) (locally . ,body))))
       (((funcall multiple-value-call) function &rest args)
        (with-propagated-subform-call/cc-p
          (conditional-call/cc
           `(,(car form) ,(propagate-funcall-function-has-call/cc-p (walk function env))
             . ,(mapcar (compose
                         (ecase (car form)
                           (multiple-value-call (lambda (form)
                                                  (if (and (listp form) (eq (car form) 'cont:without-call/cc))
                                                      `(progn . ,(cdr form)) form)))
                           (funcall #'identity))
                         (rcurry #'walk env))
                        args)))))
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
            (macrolet ((with-lexical-tags (&body body)
                         `(let ((*lexcial-tags* (nconc (mapcar (rcurry #'cons *subform-has-call/cc-p*) tags) *lexcial-tags*)))
                            ,@body)))
              (with-lexical-tags (mapc (rcurry #'walk env) body))
              (with-lexical-tags (conditional-call/cc `(tagbody . ,(remove-if #'null (optimize-body (mapcar (rcurry #'walk env) body))))))))))
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
           `(,(car form) . ,(mapcar (rcurry #'walk env) args))
           form)))))
    (t form)))

(defmacro %%with-cont-optimizer (&body body &environment env)
  `(cont:with-call/cc . ,(mapcar (rcurry #'walk env) body)))

(defmacro %with-cont-optimizer ((tags functions blocks) &body body &environment env &aux (*subform-has-call/cc-p* nil))
  (if *top-level-optimizer-p*
      (let ((*top-level-optimizer-p* nil)
            (*lexcial-tags* tags)
            (*lexcial-functions* functions)
            (*lexcial-blocks* blocks))
        (funcall (macro-function '%%with-cont-optimizer) `(%%with-cont-optimizer . ,body) env))
      `(progn . ,body)))

(defvar *subform-modified-p* nil)

(defmacro with-propagated-subform-modified-p (&body body)
  (with-gensyms (pred)
    `(let ((,pred nil))
       (multiple-value-prog1
           (let ((*subform-modified-p* nil))
             (multiple-value-prog1 (progn . ,body)
               (setf ,pred *subform-modified-p*)))
         (unless *subform-modified-p*
           (setf *subform-modified-p* ,pred))))))

(defmacro with-protected-subform-modified-p (&body body)
  `(let ((*subform-modified-p* nil)) . ,body))

(defun conditional-modified-form (form &optional (unmodified-form form))
  (if *subform-modified-p* form unmodified-form))

(defun funcall-to-multiple-value-call (form)
  (labels ((funcall-to-multiple-value-call (form)
             (with-propagated-subform-modified-p
               (conditional-modified-form
                (typecase form
                  ((and proper-list cons)
                   (destructuring-case form
                     ((funcall function &rest args)
                      (if (and (= (length args) 1)
                               (loop :for arg := (car args) :then (cadr arg)
                                     :while (listp arg)
                                     :while (member (car arg) '(progn locally))
                                     :when (eq (cadr arg) +without-call/cc-mark+)
                                       :return t))
                          (progn
                            (setf *subform-modified-p* t)
                            `(multiple-value-call . ,(mapcar #'funcall-to-multiple-value-call (cons function args))))
                          `(funcall . ,(mapcar #'funcall-to-multiple-value-call (cons function args)))))
                     ((t &rest args) (declare (ignore args))
                      (mapcar #'funcall-to-multiple-value-call form))))
                  (t form))
                form))))
    (with-protected-subform-modified-p (funcall-to-multiple-value-call form))))

(defmacro with-cont-optimizer (&body body &environment env)
  (if *top-level-optimizer-p*
      (progn
        (when *allow-multiple-value-p*
          (multiple-value-bind (form supportp)
              (macroexpand-all
               `(%with-cont-optimizer (nil nil nil) . ,body)
               #-(or ecl sbcl) env
               #+sbcl #.(if (string= (lisp-implementation-version) "2.4.3")
                            '(when env
                              (sb-c::make-lexenv
                               :policy (sb-c::process-optimize-decl '(optimize (sb-c:jump-table 0)) (sb-c::lexenv-policy env))
                               :default env))
                            'env))
            (if supportp
                (setf body `(symbol-macrolet ((,+without-call/cc-mark+ nil))
                              ,(funcall-to-multiple-value-call form)))
                (progn
                  (warn "The current Lisp implementation does not support MACROEXPAND-ALL, therefore CL-CONT-OPTIMIZER may discard return values other than the first one.")
                  (setf *allow-multiple-value-p* nil)))))
        (unless *allow-multiple-value-p*
          (setf body `(%with-cont-optimizer (nil nil nil) . ,body))))
      (setf body `(progn . ,body)))
  (values body))
