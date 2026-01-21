(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - PROBLEM STATEMENT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem: Let m_0 and n_0 be distinct positive integers. For every
;;; positive integer k, define m_k and n_k to be the relatively prime
;;; positive integers such that
;;;
;;;     m_k / n_k = (2*m_{k-1} + 1) / (2*n_{k-1} + 1)
;;;
;;; Prove that 2*m_k + 1 and 2*n_k + 1 are relatively prime for all
;;; but finitely many positive integers k.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "projects/numbers/euclid" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SEQUENCE DEFINITION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reduce a fraction num/den to lowest terms, returning (m . n) where gcd(m,n)=1
(defun reduce-to-lowest-terms (num den)
  (declare (xargs :guard (and (posp num) (posp den))))
  (let ((g (dm::gcd num den)))
    (cons (/ num g) (/ den g))))

;; One step of the sequence: given (m_{k-1}, n_{k-1}), compute (m_k, n_k)
;; where m_k/n_k = (2*m_{k-1}+1)/(2*n_{k-1}+1) in lowest terms
(defun next-mn (m n)
  (declare (xargs :guard (and (posp m) (posp n))))
  (reduce-to-lowest-terms (+ (* 2 m) 1)
                          (+ (* 2 n) 1)))

;; The k-th pair (m_k, n_k) in the sequence
(defun mn-seq (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (if (zp k)
      (cons m0 n0)
    (let ((prev (mn-seq m0 n0 (1- k))))
      (next-mn (car prev) (cdr prev)))))

;; m_k accessor
(defun m-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (car (mn-seq m0 n0 k)))

;; n_k accessor
(defun n-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (cdr (mn-seq m0 n0 k)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; THE THEOREM TO PROVE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; "For all but finitely many k" means:
;;; There exists N such that for all k >= N, the property holds.
;;;
;;; In ACL2, we express this as: there exists a function that computes
;;; a bound N (depending on m0, n0) such that the property holds for k >= N.

;; The property we want: gcd(2*m_k + 1, 2*n_k + 1) = 1
(defun coprime-transformed-p (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (equal (dm::gcd (+ (* 2 (m-k m0 n0 k)) 1)
                  (+ (* 2 (n-k m0 n0 k)) 1))
         1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MAIN THEOREM (to be proven)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; There exists a computable bound N(m0, n0) such that for all k >= N,
;;; gcd(2*m_k + 1, 2*n_k + 1) = 1.
;;;
;;; In ACL2, this is stated by defining a witness function `bound-N`
;;; and proving the theorem below.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The bound function (to be defined as part of the proof)
;; For now, we leave it as a stub - the proof must provide this.
(defstub bound-N (m0 n0) t)

;;; PUTNAM 2025 A1 - MAIN THEOREM
;;;
;;; For distinct positive integers m0, n0, there exists N such that
;;; for all k >= N, gcd(2*m_k + 1, 2*n_k + 1) = 1.

(defthm putnam-2025-a1-main
  (implies (and (posp m0)
                (posp n0)
                (not (equal m0 n0))
                (natp k)
                (>= k (bound-N m0 n0)))
           (coprime-transformed-p m0 n0 k))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; NOTES ON THE FORMALIZATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; 1. The sequence is well-defined: starting from distinct positive
;;;    integers, each step produces a reduced fraction of positive integers.
;;;
;;; 2. The conclusion "for all but finitely many k" is formalized as
;;;    the existence of a bound N. The proof must:
;;;    (a) Define what bound-N actually is (replace the defstub)
;;;    (b) Prove the theorem for that concrete definition
;;;
;;; 3. Key insight from the problem: Let g_k = gcd(2*m_k+1, 2*n_k+1).
;;;    Since 2*m_k+1 and 2*n_k+1 are both odd, g_k is odd.
;;;    The g_k divides (2*m_k+1) - (2*n_k+1) = 2*(m_k - n_k).
;;;    Since g_k is odd, g_k divides (m_k - n_k).
;;;
;;; 4. The bound N is related to the odd part of |m0 - n0|:
;;;    each time g_k > 1, the odd part of |m_k - n_k| strictly decreases,
;;;    so after finitely many steps, the difference becomes a power of 2,
;;;    and then g_k = 1 forever.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

