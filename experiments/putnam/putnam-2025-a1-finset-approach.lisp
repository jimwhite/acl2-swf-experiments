;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; putnam-2025-a1-finset-approach.lisp
;;;
;;; ACL2 translation of Lean4 Putnam 2025 A1 proof using the
;;; Finset.prod approach (products over finite index sets as lists).
;;;
;;; Based on recommendations from "ACL2 Equivalent of Lean4's Finset.prod"
;;;
;;; THEOREM (Putnam 2025 A1):
;;;   For distinct positive integers m0, n0, the set
;;;   {k | gcd(2*m_k+1, 2*n_k+1) > 1} is finite.
;;;
;;; ACL2 FORMULATION:
;;;   For all k >= bound-N(m0, n0), we have gcd(2*m_k+1, 2*n_k+1) = 1
;;;   where bound-N = odd-part(|m0 - n0|)
;;;
;;; Author: Claude (translation from Lean4)
;;; Date: January 2026
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "projects/numbers/euclid" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: BASIC DEFINITIONS (from Lean4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; odd-part: Remove all factors of 2 from n
;; Lean4: let oddPart : ℕ → ℕ := fun n => n / 2 ^ n.factorization 2
(defun odd-part (n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (or (zp n) (not (integerp (/ n 2))))
      n
    (odd-part (/ n 2))))

;; Sequence step: (m', n') where m'/n' = (2m+1)/(2n+1) reduced
;; Lean4: m (k+1) = ((2*m k+1)/(2*n k+1) : ℚ).num
(defun next-mn (m n)
  (declare (xargs :guard (and (posp m) (posp n))
                  :verify-guards nil))
  (let* ((a (+ 1 (* 2 m)))
         (b (+ 1 (* 2 n)))
         (g (dm::gcd a b)))
    (cons (/ a g) (/ b g))))

;; Full sequence (m_k, n_k)
(defun mn-seq (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :measure (nfix k)
                  :verify-guards nil))
  (if (zp k)
      (cons m0 n0)
    (let ((prev (mn-seq m0 n0 (1- k))))
      (next-mn (car prev) (cdr prev)))))

(defun m-k (m0 n0 k) (car (mn-seq m0 n0 k)))
(defun n-k (m0 n0 k) (cdr (mn-seq m0 n0 k)))

;; g(k) = gcd(2*m_k+1, 2*n_k+1)
;; Lean4: let g : ℕ → ℕ := fun k => (2 * m k + 1).gcd (2 * n k + 1)
(defun g-k (m0 n0 k)
  (let ((m (m-k m0 n0 k))
        (n (n-k m0 n0 k)))
    (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))))

;; D(k) = |m_k - n_k|
;; Lean4: let D : ℕ → ℕ := fun k => if m k ≥ n k then m k - n k else n k - m k
(defun D-k (m0 n0 k)
  (abs (- (m-k m0 n0 k) (n-k m0 n0 k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: FINSET.PROD EQUIVALENT (from recommendations)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Product of g(k) over consecutive indices 0..k-1
;; Lean4: (Finset.range K).prod g
(defun prod-g (m0 n0 k)
  "Product of g(0), g(1), ..., g(k-1)"
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :measure (nfix k)
                  :verify-guards nil))
  (if (zp k)
      1
    (* (g-k m0 n0 (1- k)) (prod-g m0 n0 (1- k)))))

;; Product of g(k) over arbitrary list of indices
;; This is the ACL2 Finset.prod equivalent for non-consecutive indices
(defun prod-g-over-list (m0 n0 indices)
  "Product of g(k) for each k in indices (a list of naturals)"
  (declare (xargs :guard (and (posp m0) (posp n0))
                  :verify-guards nil))
  (if (atom indices)
      1
    (* (g-k m0 n0 (car indices))
       (prod-g-over-list m0 n0 (cdr indices)))))

;; The bound N after which all g(k) = 1
(defun bound-N (m0 n0)
  (odd-part (abs (- m0 n0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: KEY LEMMAS (corresponding to Lean4 proof)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LEMMA: gcd is positive
(defthm gcd-posp
  (implies (and (posp a) (posp b))
           (posp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x a) (y b)))))
  :rule-classes (:rewrite :type-prescription))

;; LEMMA: gcd divides both arguments
(defthm gcd-divides-first
  (implies (and (integerp a) (integerp b) (not (= a 0)))
           (dm::divides (dm::gcd a b) a))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))))))

(defthm gcd-divides-second
  (implies (and (integerp a) (integerp b) (not (= b 0)))
           (dm::divides (dm::gcd a b) b))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))))))

;; LEMMA: 2n+1 is odd
(defthm two-n-plus-one-odd
  (implies (natp n)
           (not (integerp (/ (+ 1 (* 2 n)) 2)))))

;; LEMMA: 3^{n+1} > n (key bound for contradiction)
(defun three-pow (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 1 (* 3 (three-pow (1- n)))))

(defthm three-pow-greater-than-n
  (implies (posp n)
           (< n (three-pow (1+ n))))
  :hints (("Goal" :induct (three-pow n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 4: THE KEY RECURRENCE (Lean4: hD_rec)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; D(k+1) * g(k) = 2 * D(k)
;;;
;;; This follows from:
;;;   g(k) * m(k+1) = 2*m(k) + 1
;;;   g(k) * n(k+1) = 2*n(k) + 1
;;;   
;;; Therefore:
;;;   g(k) * (m(k+1) - n(k+1)) = 2*(m(k) - n(k))
;;;   g(k) * D(k+1) = 2 * D(k)
;;;
;;; (Assuming signs work out - need to handle both cases m>n and n>m)

;; These lemmas establish the recurrence (proofs needed)
;; (defthm g-times-m-next ...)
;; (defthm g-times-n-next ...)
;; (defthm D-recurrence ...)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: ODDPART DESCENT (Lean4: hoddPart_descent)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; odd-part(D(K)) * prod-g(K) = odd-part(D(0))
;;;
;;; This is the KEY invariant. It implies:
;;; - prod-g(K) divides odd-part(D(0)) 
;;; - prod-g(K) <= odd-part(D(0)) <= D(0)
;;;
;;; PROOF SKETCH:
;;; Base case K=0: odd-part(D(0)) * 1 = odd-part(D(0)) ✓
;;; Inductive step: 
;;;   From D(k+1) * g(k) = 2 * D(k), we get
;;;   odd-part(D(k+1)) * g(k) = odd-part(D(k))
;;;   (because g(k) is odd, so it factors out of odd-part)
;;;   
;;;   So: odd-part(D(k+1)) * prod-g(k+1)
;;;     = odd-part(D(k+1)) * g(k) * prod-g(k)
;;;     = odd-part(D(k)) * prod-g(k)
;;;     = odd-part(D(0))  by IH

;; (defthm oddpart-descent ...)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: THE BOUND (Lean4: hprod_bound)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; prod-g-over-list(indices) <= D(0)
;;;
;;; For any finite list of indices, the product of g values over those
;;; indices is bounded by D(0).
;;;
;;; PROOF:
;;; Let K = 1 + max(indices). Then:
;;; - prod-g-over-list(indices) divides prod-g(K)
;;;   (because the g values at indices are a subset of g(0)..g(K-1))
;;; - prod-g(K) divides odd-part(D(0))  (by oddpart descent)
;;; - odd-part(D(0)) <= D(0)
;;;
;;; Therefore prod-g-over-list(indices) <= D(0).

;; (defthm prod-g-over-list-bounded ...)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 7: MAIN THEOREM (Lean4: putnam_2025_a1)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; THEOREM: For all k >= bound-N(m0, n0), g(k) = 1.
;;;
;;; PROOF BY CONTRADICTION:
;;; Suppose there exist D(0)+1 indices k_1 < k_2 < ... < k_{D(0)+1}
;;; where g(k_i) > 1 for each i.
;;;
;;; Since g(k_i) is the gcd of two odd numbers and > 1, we have g(k_i) >= 3.
;;;
;;; Product over these indices:
;;;   prod-g-over-list((k_1, ..., k_{D(0)+1})) >= 3^{D(0)+1}
;;;
;;; But by the bound:
;;;   prod-g-over-list((k_1, ..., k_{D(0)+1})) <= D(0)
;;;
;;; Since 3^{D(0)+1} > D(0) (proved above), we have a contradiction.
;;;
;;; Therefore, there are at most D(0) "bad" indices.
;;; Equivalently, for all k >= D(0), g(k) = 1.
;;;
;;; (Actually, the bound is odd-part(D(0)) which may be smaller than D(0).)

;; MAIN THEOREM (statement - proof requires all the above lemmas)
;; (defthm putnam-2025-a1
;;   (implies (and (posp m0) (posp n0) (not (= m0 n0))
;;                 (natp k)
;;                 (>= k (bound-N m0 n0)))
;;            (equal (g-k m0 n0 k) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SUMMARY: WHAT REMAINS TO PROVE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; 1. D-recurrence: D(k+1) * g(k) = 2 * D(k)
;;;    - Needs lemmas about next-mn preserving positivity
;;;    - Handle both m > n and n > m cases
;;;
;;; 2. oddpart-descent: odd-part(D(K)) * prod-g(K) = odd-part(D(0))
;;;    - Induction using D-recurrence
;;;    - Need: odd divisor of n divides odd-part(n)
;;;
;;; 3. prod-g-over-list-bounded: prod-g-over-list(indices) <= D(0)
;;;    - Follows from oddpart-descent
;;;    - Need: product over subset divides product over superset
;;;
;;; 4. bad-g-geq-3: g(k) > 1 implies g(k) >= 3
;;;    - Because g(k) divides odd numbers, so g(k) is odd
;;;    - g(k) > 1 and g(k) odd implies g(k) >= 3
;;;
;;; 5. putnam-2025-a1: For k >= bound-N, g(k) = 1
;;;    - Contradiction argument using 3^{n+1} > n
;;;
;;; The key insight from the Finset.prod approach is that
;;; prod-g-over-list provides a way to talk about products
;;; over arbitrary (non-consecutive) finite index sets.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
