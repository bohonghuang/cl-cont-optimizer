(defpackage cl-cont-optimizer.test
  (:use #:cl #:parachute #:cl-cont #:cl-cont-optimizer))

(in-package #:cl-cont-optimizer.test)

(define-test suite)

(defun make-index-generator (from &optional to)
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
          (setf next-element #'next
                generate (lambda () (call/cc next-element))))
        generate))))

(defun make-list-iterator (list)
  (with-cont-optimizer
    (with-call/cc
      (let ((next-element #'values)
            (generate #'values))
        (declare (type function next-element generate))
        (flet ((next (return-cc)
                 (declare (type function return-cc))
                 (dolist (elem list)
                   (setf return-cc
                         (call/cc (lambda (next-cc)
                                    (setf next-element next-cc)
                                    (funcall return-cc elem)))))
                 (funcall return-cc nil)))
          (setf next-element #'next
                generate (lambda () (call/cc next-element))))
        generate))))

(defun iterator-list (iterator)
  (loop :for item := (funcall iterator)
        :while item
        :collect item))

(defvar *test-list* nil)

(define-test index-generator :parent suite
  (let ((expected (loop :for i :from 1 :to 100 :collect i)))
    (is equal expected (setf *test-list* (iterator-list (make-index-generator 1 100))))))

(define-test list-iterator :parent suite :depends-on (index-generator)
  (let ((iterator (make-list-iterator *test-list*)))
    (is equal *test-list* (iterator-list iterator))))

