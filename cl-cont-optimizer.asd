(defsystem cl-cont-optimizer
  :version "1.0.0"
  :author "Bohong Huang <1281299809@qq.com>"
  :maintainer "Bohong Huang <1281299809@qq.com>"
  :license "Apache-2.0"
  :description "An optimizer designed for cl-cont to reduce the amount of code for CPS transformation."
  :homepage "https://github.com/bohonghuang/cl-cont-optimizer"
  :bug-tracker "https://github.com/bohonghuang/cl-cont-optimizer/issues"
  :source-control (:git "https://github.com/bohonghuang/cl-cont-optimizer.git")
  :components ((:file "package"))
  :depends-on (#:alexandria #:cl-cont #:trivial-macroexpand-all)
  :in-order-to ((test-op (test-op #:cl-cont-optimizer/test))))

(defsystem cl-cont-optimizer/test
  :depends-on (#:cl-cont-optimizer #:parachute)
  :pathname "./test/"
  :components ((:file "package"))
  :perform (test-op (op c) (symbol-call '#:parachute '#:test (find-symbol (symbol-name '#:suite) '#:cl-cont-optimizer.test))))
