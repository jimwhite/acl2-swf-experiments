; Simple test file for acl2-mcp certification with FTY and SMTLink

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "projects/smtlink/top" :dir :system :ttags :all)

(value-triple (tshell-ensure))

; Define a simple FTY product type
(fty::defprod point
  ((x-coord integerp :default 0)
   (y-coord integerp :default 0)))

; A simple function on points
(define point-sum ((p point-p))
  :returns (sum integerp)
  (+ (point->x-coord p) (point->y-coord p)))

; A simple theorem (pure ACL2)
(defthm point-sum-type
  (implies (point-p p)
           (integerp (point-sum p))))

; A simple theorem using SMTLink
(defthm simple-arithmetic-smt
  (implies (and (integerp x)
                (integerp y)
                (< 0 x)
                (< 0 y))
           (< 0 (+ x y)))
  :hints (("Goal" :smtlink nil)))
