(in-package "ACL2")

;; =============================================================================
;; Real Challenge Problems from Software Foundations (Early Chapters)
;; =============================================================================
;;
;; This file contains SWF exercises that are GENUINELY CHALLENGING in ACL2.
;; After auditing all 3-4 star exercises from SWF chapters 2-5, only these
;; require non-trivial effort in ACL2.
;;
;; Criteria for inclusion:
;; - Requires helper lemmas, careful induction, or theory control
;; - Not solved automatically by ACL2's built-in automation
;; - Can be properly expressed in ACL2 (no higher-order function issues)
;;
;; Excluded exercises:
;; - Bags/Interleaving: Trivial in ACL2 (see trivial-swf-exercises.lisp)
;; - Church Numerals: Can't encode properly without higher-order functions
;; - Currying: Can't state properly without lambdas in theorems
;;
;; LEGEND:
;; ✓ SWF - Theorem appears in Software Foundations
;; ⚠ ADAPTED - Based on SWF but modified for ACL2
;; ✗ INVENTED - Created for this file (may be helper lemma)
;; ★ - Difficulty rating (★☆☆☆ = easy, ★★★★ = hard)
;;
;; =============================================================================


;; =============================================================================
;; CHALLENGE 1: Binary Number System (★★★★ HARD)
;; =============================================================================
;; Source: Software Foundations, Induction chapter
;; Difficulty: HARD - Custom data type requires termination proofs
;;
;; Build a complete binary number system with conversion to/from naturals
;; and prove properties about normalization and arithmetic.
;;
;; Why this is hard:
;; - Custom recursive data type (not built-in like lists)
;; - Functions won't admit without measure hints
;; - Need to establish basic properties before proving main theorems
;; - Round-trip conversions require careful reasoning about normalization
;; =============================================================================

;; Binary numbers: either Zero, or a sequence of bits (least significant first)
;; Representation: Bin ::= Z | B0 Bin | B1 Bin
;; Examples: 0 = Z, 1 = (B1 . Z), 2 = (B0 B1 . Z), 3 = (B1 B1 . Z)
;;
;; This representation allows leading zeros: (B0 B0 B1 . Z) = 4
;; Normalization removes them: normalize((B0 B0 B1 . Z)) = (B1 . Z) = 2... wait that's wrong
;; Actually (B0 B1 . Z) = 2 because it's LSB first: bit_0 + 2*bit_1 = 0 + 2*1 = 2

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

;; =============================================================================
;; CHALLENGE THEOREMS - BINARY NUMBERS
;; =============================================================================

;; ✓ SWF: bin_to_nat_pres_incr (★★★☆ HARD)
;; Theorem: Incrementing preserves the numeric value correctly
;;
;; Strategy hints:
;; - Will likely need lemmas about binp preservation
;; - May need arithmetic lemmas about (* 2 (+ 1 n))
;; - Induction on structure of binary number
(defthm bin-incr-correct
  (implies (binp b)
           (equal (bin-to-nat (bin-incr b))
                  (+ 1 (bin-to-nat b)))))

;; ✓ SWF: nat_bin_nat (★★★★ HARD)
;; Theorem: Converting nat -> bin -> nat is identity
;;
;; Strategy hints:
;; - Requires bin-incr-correct as lemma
;; - Induction on natural number n
;; - This is easier direction than bin_nat_bin
(defthm nat-bin-nat
  (implies (natp n)
           (equal (bin-to-nat (nat-to-bin n))
                  n)))

;; ⚠ ADAPTED: Implied by SWF's double_incr_bin (★★★☆ HARD)
;; Theorem: Doubling corresponds to multiplication by 2
;;
;; Strategy hints:
;; - May need lemma about (+ x x) = (* 2 x)
;; - Consider what happens when b = Z
(defthm bin-double-correct
  (implies (binp b)
           (equal (bin-to-nat (bin-double b))
                  (* 2 (bin-to-nat b)))))

;; ✗ INVENTED: Useful helper lemma (★★★☆ MODERATE)
;; Theorem: Normalization preserves numeric value
;;
;; Strategy hints:
;; - Induction on structure of b
;; - Need to reason about what happens when rest normalizes to Z
;; - Consider cases: bit is B0 vs B1
(defthm bin-normalize-preserves-value
  (implies (binp b)
           (equal (bin-to-nat (bin-normalize b))
                  (bin-to-nat b))))

;; ✓ SWF: bin_nat_bin (★★★★★ VERY HARD - not required initially)
;; Theorem: Converting bin -> nat -> bin normalizes the binary number
;;
;; This is the hard direction! Requires all previous lemmas plus careful
;; reasoning about what "normalized" means structurally.
;;
;; (defthm bin-nat-bin
;;   (implies (binp b)
;;            (equal (nat-to-bin (bin-to-nat b))
;;                   (bin-normalize b))))


;; =============================================================================
;; CHALLENGE 2: Function Injectivity (★★★☆ MODERATE)
;; =============================================================================
;; Source: Software Foundations, Lists chapter
;; Difficulty: MODERATE - Requires reasoning about inverses
;;
;; Prove that certain functions are injective (one-to-one).
;; An injective function maps distinct inputs to distinct outputs:
;;   f(x1) = f(x2) → x1 = x2
;;
;; Why this is moderately challenging:
;; - Need to reason about function inverses
;; - May require helper lemmas about reverse being involutive
;; - Different proof strategies for specific vs general injectivity
;; =============================================================================

;; ✓ SWF: rev_injective (★★★☆ MODERATE)
;; Theorem: Reverse is injective
;;
;; Strategy hints:
;; - Key insight: reverse is its own inverse (involution)
;; - May need lemma: (reverse (reverse l)) = l
;; - Then: if (reverse l1) = (reverse l2),
;;   apply reverse to both sides to get l1 = l2
(defthm rev-injective
  (implies (and (true-listp l1) (true-listp l2))
           (equal (equal (reverse l1) (reverse l2))
                  (equal l1 l2))))

;; ✓ SWF: involution_injective (★★★★ HARD)
;; Theorem: Any involution is injective
;;
;; In SWF, this is a general theorem:
;;   ∀ f, (∀ n, n = f(f(n))) → (∀ n1 n2, f(n1) = f(n2) → n1 = n2)
;;
;; In ACL2, we can't quantify over functions easily, so we prove it for
;; specific functions or use functional instantiation.
;;
;; Strategy hints:
;; - For specific function (like reverse), use the involution property
;; - For general case, would need defun-sk or functional instantiation
;; - Consider proving for natural number functions first (simpler case)
;;
;; Example instantiation for reverse:
(defthm involution-injective-reverse
  (implies (and (true-listp l1)
                (true-listp l2)
                ;; Involution property as hypothesis
                (equal (reverse (reverse l1)) l1)
                (equal (reverse (reverse l2)) l2))
           ;; Injectivity conclusion
           (equal (equal (reverse l1) (reverse l2))
                  (equal l1 l2))))

;; Note: For a general involution theorem, you might want to use defun-sk
;; to quantify over functions, or prove it for specific interesting cases
;; like reverse, complement, negate, etc.


;; =============================================================================
;; END OF CHALLENGE PROBLEMS
;; =============================================================================
;;
;; SUMMARY OF CHALLENGES:
;;
;; 1. Binary Numbers (4 theorems): ★★★★ HARD
;;    - Custom data type with complex structural reasoning
;;    - Requires termination proofs and measure hints
;;    - Round-trip conversion properties need careful setup
;;
;; 2. Function Injectivity (2 theorems): ★★★☆ MODERATE
;;    - Reasoning about function inverses
;;    - Good practice with bidirectional equality reasoning
;;    - Involution theorem requires insight
;;
;; TOTAL: 6 genuine challenge theorems
;;
;; LESSONS LEARNED ABOUT DIFFICULTY:
;; - Custom encodings DON'T automatically bypass automation!
;; - Peano arithmetic with custom types: Still TRIVIAL (proved automatically)
;; - Permutation relation: Also TRIVIAL (proved automatically)
;; - What matters: REASONING COMPLEXITY, not built-in vs custom types
;; - ACL2's induction heuristics work on ANY structurally recursive definition
;;
;; MOVED TO TRIVIAL FILE (proved automatically with 0 hints):
;; - Bags, Interleaving: Trivial with built-in lists
;; - Peano arithmetic: Trivial even with custom encoding!
;; - Permutation: Trivial with computational definition
;; See: experiments/trivial-swf-exercises.lisp
;;
;; EXCLUDED (can't encode properly in ACL2):
;; - Church Numerals: Requires polymorphic higher-order functions
;; - Currying: Requires lambdas in theorem statements
;;
;; NEXT STEPS:
;; 1. Attempt binary number theorems (genuinely hard)
;; 2. Prove reverse injectivity (good moderate challenge)
;; 3. Tackle involution theorem (requires insight)
;;
;; These are the REAL challenges - they require thought, helper lemmas,
;; and understanding of ACL2's proof strategies.
;; =============================================================================
