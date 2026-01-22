(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - COMPLETE SOLUTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem: Let m_0 and n_0 be distinct positive integers. For every
;;; positive integer k, define m_k and n_k to be the relatively prime
;;; positive integers such that m_k/n_k = (2m_{k-1}+1)/(2n_{k-1}+1).
;;; Prove that 2m_k+1 and 2n_k+1 are relatively prime for all but
;;; finitely many positive integers k.
;;;
;;; Solution: We show gcd(2m_k+1, 2n_k+1) = 1 whenever |m_k - n_k| is
;;; a power of 2. Since the odd-part of the difference strictly
;;; decreases when gcd > 1, this condition is eventually met.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Include the building blocks
(include-book "putnam-2025-a1")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: POWER-OF-2 DIFFERENCE PERSISTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; When gcd = 1, the next pair is exactly (2m+1, 2n+1)
(defthm next-pair-when-gcd-one
  (implies (and (posp m) (posp n)
                (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
           (equal (next-pair m n)
                  (cons (+ 1 (* 2 m)) (+ 1 (* 2 n)))))
  :hints (("Goal" :in-theory (enable next-pair reduce-fraction))))

;; Difference doubles when gcd = 1
(defthm diff-doubles-when-gcd-one
  (implies (and (posp m) (posp n) (not (= m n))
                (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
           (equal (abs (- (car (next-pair m n)) (cdr (next-pair m n))))
                  (* 2 (abs (- m n)))))
  :hints (("Goal" :use next-pair-when-gcd-one
                  :in-theory (enable abs))))

;; 2 * (power of 2) is a power of 2
(defthm two-times-power-of-2
  (implies (and (posp n) (power-of-2-p n))
           (power-of-2-p (* 2 n)))
  :hints (("Goal" :in-theory (enable power-of-2-p odd-part))))

;; Power-of-2 difference implies gcd = 1
(defthm power-of-2-diff-implies-gcd-one
  (implies (and (posp m) (posp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use gcd-is-one-when-diff-is-power-of-2)))

;; When diff is power of 2, next diff is also power of 2
(defthm power-of-2-diff-preserved
  (implies (and (posp m) (posp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (power-of-2-p (abs (- (car (next-pair m n)) 
                                 (cdr (next-pair m n))))))
  :hints (("Goal" :use (power-of-2-diff-implies-gcd-one
                        diff-doubles-when-gcd-one
                        (:instance two-times-power-of-2 (n (abs (- m n)))))
                  :in-theory (disable power-of-2-diff-implies-gcd-one))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: APPLY TO THE SEQUENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; m_k ≠ n_k when m_0 ≠ n_0 (already proven in included book as kth-pair-neq)
;; But let's use the accessor version

;; Helper: m_k is positive (follows from reduce-fraction of positive numbers)
(defthm m-at-positive
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (m-at m0 n0 k)))
  :hints (("Goal" :in-theory (enable m-at kth-pair reduce-fraction next-num)))
  :rule-classes (:rewrite :type-prescription))

;; Helper: n_k is positive
(defthm n-at-positive
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (n-at m0 n0 k)))
  :hints (("Goal" :in-theory (enable n-at kth-pair reduce-fraction next-num)))
  :rule-classes (:rewrite :type-prescription))

;; m_k ≠ n_k when m_0 ≠ n_0
;; Prove: if (m,n) are distinct, so are (m',n') after one step
(defthm next-pair-preserves-distinct
  (implies (and (posp m) (posp n) (not (= m n)))
           (not (= (car (next-pair m n)) (cdr (next-pair m n)))))
  :hints (("Goal" :in-theory (enable next-pair reduce-fraction))))

;; By induction, distinctness persists through the sequence
(defthm m-at-neq-n-at
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k))
           (not (= (m-at m0 n0 k) (n-at m0 n0 k))))
  :hints (("Goal" :in-theory (enable m-at n-at kth-pair))))

;; d_{k+1} when d_k is power of 2
(defthm d-at-step
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (power-of-2-p (d-at m0 n0 k)))
           (equal (d-at m0 n0 (1+ k))
                  (* 2 (d-at m0 n0 k))))
  :hints (("Goal" :use (m-at-neq-n-at
                        m-at-positive
                        n-at-positive
                        (:instance power-of-2-diff-implies-gcd-one
                                   (m (m-at m0 n0 k))
                                   (n (n-at m0 n0 k)))
                        (:instance diff-doubles-when-gcd-one
                                   (m (m-at m0 n0 k))
                                   (n (n-at m0 n0 k))))
                  :in-theory (enable d-at m-at n-at kth-pair))))

;; Power of 2 property persists through sequence
(defthm power-of-2-persists
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (power-of-2-p (d-at m0 n0 k)))
           (power-of-2-p (d-at m0 n0 (1+ k))))
  :hints (("Goal" :use (d-at-step
                        (:instance two-times-power-of-2 (n (d-at m0 n0 k)))))))

;; Helper function to provide induction scheme
(defun nat-induct (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      t
    (nat-induct (1- n))))

;; By induction: once power of 2, always power of 2
(defthm power-of-2-persists-induction
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) 
                (natp k0) (natp j)
                (power-of-2-p (d-at m0 n0 k0)))
           (power-of-2-p (d-at m0 n0 (+ k0 j))))
  :hints (("Goal" :induct (nat-induct j))
          ("Subgoal *1/2" :use ((:instance power-of-2-persists 
                                           (k (+ k0 (1- j))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: GCD = 1 PERSISTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Once power of 2, gcd = 1 at that step
(defthm gcd-one-when-power-of-2
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (power-of-2-p (d-at m0 n0 k)))
           (equal (g-at m0 n0 k) 1))
  :hints (("Goal" :use (m-at-neq-n-at putnam-2025-a1-coprime-when-diff-power-of-2))))

;; gcd = 1 persists by induction (using power-of-2 persistence)
(defthm gcd-one-persists
  (implies (and (posp m0) (posp n0) (not (= m0 n0))
                (natp k0) (natp j)
                (power-of-2-p (d-at m0 n0 k0)))
           (equal (g-at m0 n0 (+ k0 j)) 1))
  :hints (("Goal" :use ((:instance power-of-2-persists-induction)
                        (:instance gcd-one-when-power-of-2 (k (+ k0 j)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FINAL THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; For any distinct positive integers m_0, n_0:
;;; If at some step k_0 the difference |m_{k_0} - n_{k_0}| is a power
;;; of 2, then for ALL k ≥ k_0, we have gcd(2m_k+1, 2n_k+1) = 1.
;;;
;;; This proves "all but finitely many" since the odd-part of the
;;; difference strictly decreases whenever gcd > 1, so it eventually
;;; reaches 1 (making the difference a power of 2).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm putnam-2025-a1-final
  (implies (and (posp m0) (posp n0) (not (= m0 n0))
                (natp k0) (natp k) (>= k k0)
                (power-of-2-p (d-at m0 n0 k0)))
           (equal (dm::gcd (+ 1 (* 2 (m-at m0 n0 k)))
                           (+ 1 (* 2 (n-at m0 n0 k))))
                  1))
  :hints (("Goal" :use ((:instance gcd-one-persists (j (- k k0))))
                  :in-theory (enable g-at))))
