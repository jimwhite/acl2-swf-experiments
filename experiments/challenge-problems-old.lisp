(in-package "ACL2")

;; =============================================================================
;; Challenge Problems from Software Foundations (Early Chapters)
;; =============================================================================
;;
;; This file contains difficult theorem challenges from SWF Chapters 2-5.
;; These problems are either marked as 3-4 stars in SWF or involve building
;; custom types and operations to make them challenging.
;;
;; LEGEND:
;; ✓ SWF - Theorem appears in Software Foundations with same/similar statement
;; ⚠ ADAPTED - Based on SWF but modified for ACL2 or extended beyond original
;; ✗ INVENTED - Not in SWF, created for this file (may be true or FALSE!)
;; [FALSE] - Theorem is actually false (discovered via proof attempt)
;;
;; =============================================================================

;; =============================================================================
;; CHALLENGE 1: Binary Number System (from Induction chapter)
;; =============================================================================
;; Build a complete binary number system with conversion to/from naturals
;; and prove properties about normalization and arithmetic.

;; Binary numbers: either Zero, or a sequence of bits terminated by 1
;; Representation: Bin ::= Z | B0 Bin | B1 Bin
;; Examples: 0 = Z, 1 = B1(Z), 2 = B0(B1(Z)), 3 = B1(B1(Z))

(defun binp (x)
  "Recognizer for binary numbers"
  (declare (xargs :guard t))
  (if (atom x)
      (eq x 'Z)
    (and (consp x)
         (or (eq (car x) 'B0)
             (eq (car x) 'B1))
         (binp (cdr x)))))

(defun bin-incr (b)
  "Increment a binary number"
  (declare (xargs :guard (binp b)))
  (if (eq b 'Z)
      '(B1 . Z)
    (let ((bit (car b))
          (rest (cdr b)))
      (if (eq bit 'B0)
          (cons 'B1 rest)
        (cons 'B0 (bin-incr rest))))))

(defun bin-to-nat (b)
  "Convert binary number to natural number"
  (declare (xargs :guard (binp b)))
  (if (eq b 'Z)
      0
    (let ((bit (car b))
          (rest (cdr b)))
      (+ (if (eq bit 'B1) 1 0)
         (* 2 (bin-to-nat rest))))))

(defun nat-to-bin (n)
  "Convert natural number to binary"
  (declare (xargs :guard (natp n)))
  (if (zp n)
      'Z
    (bin-incr (nat-to-bin (- n 1)))))

(defun bin-normalize (b)
  "Remove leading zeros from binary number"
  (declare (xargs :guard (binp b)))
  (if (eq b 'Z)
      'Z
    (let ((bit (car b))
          (rest (cdr b)))
      (if (eq (bin-normalize rest) 'Z)
          (if (eq bit 'B0)
              'Z
            '(B1 . Z))
        (cons bit (bin-normalize rest))))))

(defun bin-double (b)
  "Double a binary number (shift left)"
  (declare (xargs :guard (binp b)))
  (if (eq b 'Z)
      'Z
    (cons 'B0 b)))

;; CHALLENGE THEOREMS:

;; ✓ SWF: bin_to_nat_pres_incr
;; 1. Prove that increment is correct
;; (defthm bin-incr-correct
;;   (implies (binp b)
;;            (equal (bin-to-nat (bin-incr b))
;;                   (+ 1 (bin-to-nat b)))))

;; ✓ SWF: nat_bin_nat
;; 2. Prove the round-trip property (nat -> bin -> nat = identity)
;; (defthm nat-bin-nat
;;   (implies (natp n)
;;            (equal (bin-to-nat (nat-to-bin n))
;;                   n)))

;; ⚠ ADAPTED: Implied by SWF's double_incr_bin but not stated exactly this way
;; 3. Prove doubling is multiplication by 2
;; (defthm bin-double-correct
;;   (implies (binp b)
;;            (equal (bin-to-nat (bin-double b))
;;                   (* 2 (bin-to-nat b)))))

;; ✗ INVENTED: Useful helper lemma, not in SWF
;; 4. Prove normalization preserves value
;; (defthm bin-normalize-preserves-value
;;   (implies (binp b)
;;            (equal (bin-to-nat (bin-normalize b))
;;                   (bin-to-nat b))))

;; Note: SWF also has bin_nat_bin which proves:
;;   nat_to_bin (bin_to_nat b) = normalize b
;; This is harder and requires the normalize function to be correct first.


;; =============================================================================
;; CHALLENGE 2: Bag (Multiset) Operations (from Lists chapter)
;; =============================================================================
;; Build a bag abstraction using lists and prove properties about counting

(defun bag-count (v bag)
  "Count occurrences of v in bag (list of natural numbers)"
  (declare (xargs :guard (and (natp v) (nat-listp bag))))
  (cond ((endp bag) 0)
        ((equal v (car bag))
         (+ 1 (bag-count v (cdr bag))))
        (t (bag-count v (cdr bag)))))

(defun bag-remove (v bag)
  "Remove one occurrence of v from bag"
  (declare (xargs :guard (and (natp v) (nat-listp bag))))
  (cond ((endp bag) nil)
        ((equal v (car bag)) (cdr bag))
        (t (cons (car bag) (bag-remove v (cdr bag))))))

(defun bag-sum (bag1 bag2)
  "Union of two bags (concatenation)"
  (declare (xargs :guard (and (nat-listp bag1) (nat-listp bag2))))
  (append bag1 bag2))

;; CHALLENGE THEOREMS:

;; ✓ SWF: remove_does_not_increase_count (✓ PROVED)
(defthm remove-does-not-increase-count
  (implies (and (natp v) (nat-listp bag))
           (<= (bag-count v (bag-remove v bag))
               (bag-count v bag))))

;; ⚠ ADAPTED: SWF has open-ended "bag_count_sum" exercise (✓ PROVED)
;; This specific formulation (count distributes over sum) is reasonable
(defthm bag-count-sum
  (implies (and (natp v) (nat-listp bag1) (nat-listp bag2))
           (equal (bag-count v (bag-sum bag1 bag2))
                  (+ (bag-count v bag1)
                     (bag-count v bag2)))))

;; ✗ INVENTED [FALSE]: Original version was false! (✓ PROVED conditional version)
;; The original theorem (removing from both bags independently) is FALSE
;; because bag-remove only removes ONE occurrence. The correct theorem requires
;; that v is not in the first bag.
(defthm bag-remove-sum-when-not-in-first
  (implies (and (natp v)
                (nat-listp bag1)
                (nat-listp bag2)
                (equal (bag-count v bag1) 0))
           (equal (bag-remove v (bag-sum bag1 bag2))
                  (bag-sum bag1 (bag-remove v bag2)))))


;; =============================================================================
;; CHALLENGE 3: List Interleaving (from Lists chapter)
;; =============================================================================
;; Alternate elements from two lists

(defun alternate (l1 l2)
  "Interleave two lists, alternating elements"
  (declare (xargs :guard (and (true-listp l1) (true-listp l2))))
  (cond ((endp l1) l2)
        ((endp l2) l1)
        (t (cons (car l1)
                 (cons (car l2)
                       (alternate (cdr l1) (cdr l2)))))))

;; CHALLENGE THEOREMS:
;; Note: SWF only asks to implement alternate with test cases, no theorems requested

;; ✗ INVENTED: Useful property about length (✓ PROVED)
(defthm alternate-length
  (implies (and (true-listp l1) (true-listp l2))
           (equal (len (alternate l1 l2))
                  (+ (len l1) (len l2)))))

;; ✗ INVENTED: Identity properties (✓ PROVED)
(defthm alternate-nil-l
  (implies (true-listp l)
           (equal (alternate nil l) l)))

(defthm alternate-nil-r
  (implies (true-listp l)
           (equal (alternate l nil) l)))

;; ✗ INVENTED [FALSE]: Symmetry does NOT hold!
;; This theorem is FALSE. alternate is not symmetric:
;;   (alternate '(1 2) '(3 4)) = '(1 3 2 4)
;;   (alternate '(3 4) '(1 2)) = '(3 1 4 2)
;; These are not equal, so there's no symmetry property to prove.


;; =============================================================================
;; CHALLENGE 4: Function Injectivity (from Lists chapter)
;; =============================================================================
;; Prove that certain functions are injective (one-to-one)

;; CHALLENGE THEOREMS:

;; ✓ SWF: rev_injective
;; 1. Reverse is injective
;; (defthm rev-injective
;;   (implies (and (true-listp l1) (true-listp l2))
;;            (equal (equal (reverse l1) (reverse l2))
;;                   (equal l1 l2))))

;; ✓ SWF: involution_injective (adapted to reverse as example)
;; 2. If a function is its own inverse (involution), it's injective
;; Generic SWF version: ∀ f, (∀ n, n = f(f(n))) → (∀ n1 n2, f(n1) = f(n2) → n1 = n2)
;; We instantiate this for reverse:
;; (defthm involution-injective-reverse
;;   (implies (and (true-listp l1) (true-listp l2)
;;                 (equal (reverse (reverse l1)) l1)
;;                 (equal (reverse (reverse l2)) l2))
;;            (equal (equal (reverse l1) (reverse l2))
;;                   (equal l1 l2))))


;; =============================================================================
;; CHALLENGE 5: Church Numerals (from Poly chapter)
;; =============================================================================
;; Implement arithmetic using higher-order functions only
;;
;; Church encoding: A natural number n is represented as a function that
;; applies another function n times. In ACL2, we can't directly express
;; polymorphic higher-order functions, so we'll work with concrete types.

;; Church numeral: a function that takes f and x and applies f n times to x
;; We represent this as a list: (church n) applies a function n times

(defun church-apply (n f x)
  "Apply function f exactly n times to x"
  (declare (xargs :guard (natp n)))
  (if (zp n)
      x
    (church-apply (- n 1) f (f x))))

(defun church-succ-count (n)
  "Successor for Church numerals: applies function n+1 times"
  (declare (xargs :guard (natp n)))
  (+ 1 n))

(defun church-plus-count (m n)
  "Addition for Church numerals"
  (declare (xargs :guard (and (natp m) (natp n))))
  (+ m n))

(defun church-mult-count (m n)
  "Multiplication for Church numerals"
  (declare (xargs :guard (and (natp m) (natp n))))
  (* m n))

;; Helper: increment function for testing
(defun nat-succ (x)
  (declare (xargs :guard (natp x)))
  (+ 1 x))

;; CHALLENGE THEOREMS:
;; ⚠ ADAPTED: SWF has Church numeral exercises (scc, plus, mult, exp)
;; but ACL2 can't truly express polymorphic higher-order functions like Coq.
;; This encoding uses a "count" representation rather than true Church numerals.
;; The theorems below are adapted to show correctness of the encoding.

;; ⚠ ADAPTED: Based on SWF's church_scc
;; 1. Church successor is correct
;; (defthm church-succ-correct
;;   (implies (natp n)
;;            (equal (church-apply (church-succ-count n) 'nat-succ 0)
;;                   (+ 1 (church-apply n 'nat-succ 0)))))

;; ⚠ ADAPTED: Based on SWF's church_plus
;; 2. Church addition is correct
;; (defthm church-plus-correct
;;   (implies (and (natp m) (natp n))
;;            (equal (church-apply (church-plus-count m n) 'nat-succ 0)
;;                   (+ (church-apply m 'nat-succ 0)
;;                      (church-apply n 'nat-succ 0)))))

;; ⚠ ADAPTED: Based on SWF's church_mult
;; 3. Church multiplication is correct
;; (defthm church-mult-correct
;;   (implies (and (natp m) (natp n))
;;            (equal (church-apply (church-mult-count m n) 'nat-succ 0)
;;                   (* (church-apply m 'nat-succ 0)
;;                      (church-apply n 'nat-succ 0)))))

;; Note: SWF also has church_exp for exponentiation. Not included here
;; because the encoding would be even more contrived in ACL2.


;; =============================================================================
;; CHALLENGE 6: Currying and Uncurrying (from Poly chapter)
;; =============================================================================
;; Transform between functions of pairs and curried functions
;; In ACL2, we model this with explicit pair manipulation

(defun prod-curry (f pair)
  "Apply curried function f to a pair"
  (declare (xargs :guard (consp pair)))
  ;; f should be a function that takes two arguments
  ;; We'll represent this abstractly
  (list 'curry f (car pair) (cdr pair)))

(defun prod-uncurry (f x y)
  "Apply uncurried function f to two arguments"
  (declare (xargs :guard t))
  ;; f should be a function that takes a pair
  (list 'uncurry f (cons x y)))

;; CHALLENGE THEOREMS:
;; ✓ SWF: prod_curry and prod_uncurry with inverse theorems
;; However, ACL2 doesn't have true higher-order functions or lambdas in theorem
;; statements like Coq does. The challenge here is to formalize what it means
;; for curry/uncurry to be inverses in ACL2's logic.

;; ⚠ ADAPTED: Based on SWF's uncurry_curry theorem
;; SWF version: ∀ (f : X → Y → Z) x y, prod_curry (prod_uncurry f) x y = f x y
;; 1. Uncurry after curry is identity
;; (defthm uncurry-curry
;;   (implies (and (consp pair))
;;            (equal (prod-uncurry (lambda (p) (prod-curry f p))
;;                                 (car pair)
;;                                 (cdr pair))
;;                   (prod-curry f pair))))

;; ⚠ ADAPTED: Based on SWF's curry_uncurry theorem
;; SWF version: ∀ (f : (X × Y) → Z) p, prod_uncurry (prod_curry f) p = f p
;; 2. Curry after uncurry is identity
;; (defthm curry-uncurry
;;   (equal (prod-curry (lambda (x y) (prod-uncurry f x y))
;;                      (cons x y))
;;          (prod-uncurry f x y)))

;; Note: These theorems are difficult to properly state in ACL2 without
;; functional instantiation or defun-sk. They may not be worth pursuing
;; in ACL2 as the encoding doesn't capture the essence of the SWF exercise.


;; =============================================================================
;; END OF CHALLENGE PROBLEMS - AUDIT SUMMARY
;; =============================================================================
;;
;; AUDIT RESULTS (comparing to Software Foundations):
;;
;; CHALLENGE 1 (Binary Numbers):
;;   ✓ 2 theorems directly from SWF
;;   ⚠ 1 theorem adapted/implied by SWF
;;   ✗ 1 theorem invented (useful helper)
;;   DIFFICULTY: ★★★★ HARD - Functions won't even admit without measure hints!
;;   The binary representation requires proving termination of recursive functions.
;;
;; CHALLENGE 2 (Bags):
;;   ✓ 1 theorem directly from SWF (PROVED - trivial, ACL2 did it automatically)
;;   ⚠ 1 theorem from open-ended SWF exercise (PROVED - trivial)
;;   ✗ 1 theorem invented and FALSE (fixed conditional version PROVED - trivial)
;;   DIFFICULTY: ★☆☆☆ TRIVIAL - All proofs went through automatically
;;   SWF makes these hard because students build reasoning from scratch.
;;   In ACL2 with automation, these are not challenging.
;;
;; CHALLENGE 3 (List Interleaving):
;;   ✗ 3 theorems invented (2 PROVED - trivial, 1 FALSE)
;;   Note: SWF only asks to implement, no theorems requested
;;   DIFFICULTY: ★☆☆☆ TRIVIAL - Proofs trivial, finding false theorem was interesting
;;
;; CHALLENGE 4 (Function Injectivity):
;;   ✓ 2 theorems directly from SWF
;;   DIFFICULTY: ★★★☆ MODERATE - Injectivity proofs require careful reasoning
;;   May need helper lemmas about reverse being involutive.
;;
;; CHALLENGE 5 (Church Numerals):
;;   ⚠ 3 theorems adapted from SWF (encoding differs - not true Church numerals)
;;   Note: ACL2 can't express polymorphic higher-order functions like Coq
;;   DIFFICULTY: ★★☆☆ EASY-MODERATE - But encoding is so different it's not really
;;   the same exercise. These become trivial arithmetic facts with our encoding.
;;   NOT RECOMMENDED - doesn't capture the essence of SWF exercise.
;;
;; CHALLENGE 6 (Currying):
;;   ⚠ 2 theorems adapted from SWF (encoding differs - hard to state properly)
;;   Note: ACL2's lack of lambdas in theorems makes this difficult
;;   DIFFICULTY: N/A - Can't really be done properly in ACL2
;;   NOT RECOMMENDED - encoding doesn't work in ACL2.
;;
;; RECOMMENDATIONS FOR REAL CHALLENGES:
;; 1. ★★★★ Binary Numbers - Actually hard! Functions need termination proofs.
;; 2. ★★★☆ Function Injectivity - Good moderate challenge
;; 3. ★☆☆☆ Skip bags/interleaving - Too trivial with ACL2's automation
;; 4. ❌ Skip Church Numerals - Can't encode properly in ACL2
;; 5. ❌ Skip Currying - Can't encode properly in ACL2
;;
;; KEY LESSONS LEARNED:
;; 1. Two invented theorems were FALSE - formal proofs caught bad intuitions!
;; 2. SWF's "hard" exercises may be trivial in ACL2 due to automation
;; 3. SWF builds basic reasoning; ACL2 has that built-in
;; 4. Custom data types (binary) are genuinely harder in ACL2 than built-ins
;; 5. Higher-order function exercises don't translate well to ACL2
;;
;; PROVEN SO FAR: 5 theorems (3 from bags, 2 from interleaving)
;; WORTH ATTEMPTING: Binary Numbers (hard), Function Injectivity (moderate)
