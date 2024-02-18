(defpackage cl-cont-optimizer.test
  (:use #:cl #:parachute #:cl-cont #:cl-cont-optimizer))

(in-package #:cl-cont-optimizer.test)

(define-test suite)

(defun make-index-generator (from &optional to)
  (#-ecl progn #+ecl si:compiler-let #+ecl ((*allow-multiple-value-p* nil))
   ;; The MACROEXPAND-ALL in ECL doesn't expand SYMBOL-MACROLET and MACROLET.
    (with-cont-optimizer
      (with-call/cc
        (let ((next-element #'values)
              (generate #'values))
          (declare (type function next-element generate))
          (flet ((next (return-cc)
                   (declare (type function return-cc))
                   (loop :for i :from from
                         :until (and to (> i to))
                         :do (setf return-cc
                                   (call/cc (lambda (next-cc)
                                              (setf next-element next-cc)
                                              (funcall return-cc i))))
                         :finally (funcall return-cc nil))))
            (symbol-macrolet ((set-vars
                                (setf next-element #'next
                                      generate (lambda () (call/cc next-element)))))
              set-vars))
          generate)))))

(defun make-list-iterator (list)
  (#-ecl progn #+ecl si:compiler-let #+ecl ((*allow-multiple-value-p* nil))
    (with-cont-optimizer
      (with-call/cc
        (let ((next-element #'values)
              (generate #'values))
          (declare (type function next-element generate))
          (labels ((next (return-cc)
                     (declare (type function return-cc))
                     (dolist (elem list)
                       (setf return-cc
                             (call/cc (lambda (next-cc)
                                        (setf next-element next-cc)
                                        (funcall return-cc elem)))))
                     (funcall return-cc nil)))
            (macrolet ((set-vars ()
                         `(setf next-element #'next
                                generate (lambda () (call/cc next-element)))))
              (set-vars)))
          generate)))))

(defun iterator-list (iterator)
  (loop :for item := (funcall iterator)
        :while item
        :collect item))

(defvar *test-list* nil)

(define-test simple :parent suite
  (let ((continuation nil))
    (with-cont-optimizer
      (with-call/cc
        (1+ (cont:call/cc (lambda (cc) (setf continuation cc))))))
    (is = 3 (funcall continuation 2))))

(define-test index-generator :parent suite
  (let ((expected (loop :for i :from 1 :to 100 :collect i)))
    (is equal expected (setf *test-list* (iterator-list (make-index-generator 1 100))))))

(define-test list-iterator :parent suite :depends-on (index-generator)
  (let ((iterator (make-list-iterator *test-list*)))
    (is equal *test-list* (iterator-list iterator))))

(defun values-123 (&rest values)
  (let ((continuation nil))
    (with-cont-optimizer
      (with-call/cc
        (multiple-value-bind (a b c) (values 1 2 3)
          (call/cc (lambda (cc) (setf continuation cc)))
          (values-list (nconc (multiple-value-list (call/cc (lambda (cc) (funcall cc a b c)))) values)))))
    continuation))

(defmacro skip-if (pred desc &body tests)
  (let ((thunk (gensym "THUNK")))
    `(flet ((,thunk () ,@tests))
       (if ,pred
           (with-forced-status (:skipped ,@(if (listp desc) desc (list desc)))
             (,thunk))
           (,thunk)))))

(define-test multiple-value :parent suite
  (skip-if (not *allow-multiple-value-p*) "*ALLOW-MULTIPLE-VALUE-P* is NIL."
    (is-values (funcall (values-123 4 5))
      (= 1) (= 2) (= 3) (= 4) (= 5))))
