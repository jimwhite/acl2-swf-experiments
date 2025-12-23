; Advanced theorem: fold-product distributes over append
;
; SUCCESS: This file demonstrates a successful proof of fold-product-append,
; which was challenging because it requires careful control of ACL2's
; arithmetic rewriting.
;
; KEY INSIGHT: The proof succeeds by temporarily disabling commutativity-of-*
; during the main induction, then re-enabling both commutativity and
; associativity at the specific subgoal where arithmetic reasoning is needed.
; This prevents the rewriter from normalizing terms too aggressively and
; allows the arithmetic facts to apply at the right moment.

(in-package "ACL2")

; Include the base higher-order functions book
(include-book "experiment-02-higher-order")

;;; ==========================================================================
;;; Main Theorem: fold-product distributes over append
;;; ==========================================================================

; Theorem: fold-product distributes over append
; This is challenging because the inductive step requires showing:
;   (* (car l1) (* (fold-product (cdr l1)) (fold-product l2)))
;   = (* (fold-product l2) (car l1) (fold-product (cdr l1)))
;
; The proof succeeds using selective theory control:
; 1. Disable commutativity-of-* globally to prevent over-normalization
; 2. Re-enable commutativity and associativity at Subgoal *1/3''
;    where the arithmetic reasoning is needed
(defthm fold-product-append
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (equal (fold-product (append l1 l2))
                  (* (fold-product l1) (fold-product l2))))
  :hints (("Goal" :in-theory (e/d (fold-product) (commutativity-of-*)))
          ("Subgoal *1/3''" :in-theory (enable commutativity-of-* associativity-of-*))))
