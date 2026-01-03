; Higher-Order Functions for Lists
; Based on Software Foundations Chapter 5: Polymorphism (Poly)
;
; This file explores higher-order functions (map, filter, fold) in ACL2.
; Since ACL2 is fundamentally first-order, we'll work with concrete types
; rather than true polymorphism. We'll use lists of natural numbers as our
; primary example type.

(in-package "ACL2")

;;; ==========================================================================
;;; Map: Apply a function to every element of a list
;;; ==========================================================================

; map-inc: Increment every element in a list
(defun map-inc (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      nil
      (cons (+ 1 (car l))
            (map-inc (cdr l)))))

; map-square: Square every element in a list
(defun map-square (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      nil
      (cons (* (car l) (car l))
            (map-square (cdr l)))))

; General map for natural numbers (ACL2 doesn't have first-class functions,
; so we'll prove properties about specific map instances)
; For pedagogical purposes, we'll define a generic pattern that specific
; maps follow.

;;; ==========================================================================
;;; Filter: Keep only elements satisfying a predicate
;;; ==========================================================================

; filter-even: Keep only even numbers
(defun filter-even (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      nil
      (if (evenp (car l))
          (cons (car l) (filter-even (cdr l)))
          (filter-even (cdr l)))))

; filter-odd: Keep only odd numbers
(defun filter-odd (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      nil
      (if (oddp (car l))
          (cons (car l) (filter-odd (cdr l)))
          (filter-odd (cdr l)))))

;;; ==========================================================================
;;; Fold: Reduce a list to a single value
;;; ==========================================================================

; fold-sum: Sum all elements in a list (fold with + and 0)
(defun fold-sum (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      0
      (+ (car l) (fold-sum (cdr l)))))

; fold-product: Multiply all elements in a list (fold with * and 1)
(defun fold-product (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      1
      (* (car l) (fold-product (cdr l)))))

; fold-length: Count elements using fold pattern
(defun fold-length (l)
  (declare (xargs :guard (true-listp l)))
  (if (endp l)
      0
      (+ 1 (fold-length (cdr l)))))

;;; ==========================================================================
;;; Theorems about Map
;;; ==========================================================================

; Theorem: map preserves length
(defthm map-inc-preserves-length
  (equal (len (map-inc l))
         (len l)))

(defthm map-square-preserves-length
  (equal (len (map-square l))
         (len l)))

; Theorem: map distributes over append
(defthm map-inc-append
  (equal (map-inc (append l1 l2))
         (append (map-inc l1) (map-inc l2))))

(defthm map-square-append
  (equal (map-square (append l1 l2))
         (append (map-square l1) (map-square l2))))

; Theorem: map_rev - map distributes over reverse
; This is the key theorem from Software Foundations Poly chapter
; We need helper lemmas about revappend first

; Helper: map-inc distributes over revappend
(defthm map-inc-revappend
  (equal (map-inc (revappend l1 l2))
         (revappend (map-inc l1) (map-inc l2))))

(defthm map-inc-rev
  (equal (map-inc (reverse l))
         (reverse (map-inc l))))

; Helper: map-square distributes over revappend
(defthm map-square-revappend
  (equal (map-square (revappend l1 l2))
         (revappend (map-square l1) (map-square l2))))

(defthm map-square-rev
  (equal (map-square (reverse l))
         (reverse (map-square l))))

;;; ==========================================================================
;;; Theorems about Filter
;;; ==========================================================================

; Theorem: filter preserves or reduces length
(defthm filter-even-length-bound
  (<= (len (filter-even l)) (len l))
  :rule-classes :linear)

(defthm filter-odd-length-bound
  (<= (len (filter-odd l)) (len l))
  :rule-classes :linear)

; Theorem: filtering twice is idempotent
(defthm filter-even-idempotent
  (implies (nat-listp l)
           (equal (filter-even (filter-even l))
                  (filter-even l))))

(defthm filter-odd-idempotent
  (implies (nat-listp l)
           (equal (filter-odd (filter-odd l))
                  (filter-odd l))))

; Theorem: filter and append
(defthm filter-even-append
  (equal (filter-even (append l1 l2))
         (append (filter-even l1) (filter-even l2))))

(defthm filter-odd-append
  (equal (filter-odd (append l1 l2))
         (append (filter-odd l1) (filter-odd l2))))

;;; ==========================================================================
;;; Theorems about Fold
;;; ==========================================================================

; Theorem: fold-length is equivalent to built-in len
(defthm fold-length-correct
  (implies (true-listp l)
           (equal (fold-length l)
                  (len l))))

; Theorem: fold-sum of append is sum of fold-sums
(defthm fold-sum-append
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (equal (fold-sum (append l1 l2))
                  (+ (fold-sum l1) (fold-sum l2)))))

; Theorem: fold-product distributes over append
; This proof requires only associativity of multiplication, not commutativity.
; We disable commutativity-of-* to prevent the rewriter from normalizing terms
; into incompatible canonical forms. With only associativity enabled, the proof
; completes cleanly via induction.
(defthm fold-product-append
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (equal (fold-product (append l1 l2))
                  (* (fold-product l1) (fold-product l2))))
  :hints (("Goal" :in-theory (disable commutativity-of-*))))

;;; ==========================================================================
;;; Interaction between Map and Fold
;;; ==========================================================================

; Theorem: Folding after mapping
(defthm fold-sum-map-inc
  (implies (nat-listp l)
           (equal (fold-sum (map-inc l))
                  (+ (fold-sum l) (len l)))))

;;; ==========================================================================
;;; Flat Map: Map followed by concatenation
;;; ==========================================================================

; flat-map-repeat: Map each element to a list of copies
(defun repeat (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
      (cons x (repeat (- n 1) x))))

(defun flat-map-repeat (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      nil
      (append (repeat (car l) (car l))
              (flat-map-repeat (cdr l)))))

; Theorem about flat-map
(defthm flat-map-repeat-append
  (equal (flat-map-repeat (append l1 l2))
         (append (flat-map-repeat l1)
                 (flat-map-repeat l2))))
