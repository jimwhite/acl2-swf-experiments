; Simple test file for acl2-mcp certification with FTY

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)

; Define a simple FTY product type
(fty::defprod point
  ((x-coord integerp :default 0)
   (y-coord integerp :default 0)))

; A simple function on points
(define point-sum ((p point-p))
  :returns (sum integerp)
  (+ (point->x-coord p) (point->y-coord p)))

; A simple theorem
(defthm point-sum-type
  (implies (point-p p)
           (integerp (point-sum p))))
