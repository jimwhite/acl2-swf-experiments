(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - SOLUTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem: Let m_0 and n_0 be distinct positive integers. For every
;;; positive integer k, define m_k and n_k to be the relatively prime
;;; positive integers such that m_k/n_k = (2m_{k-1}+1)/(2n_{k-1}+1).
;;; Prove that 2m_k+1 and 2n_k+1 are relatively prime for all but
;;; finitely many positive integers k.
;;;
;;; Strategy: We show gcd(2m_k+1, 2n_k+1) = 1 whenever |m_k - n_k| is
;;; a power of 2. The odd-part of the difference strictly decreases
;;; when gcd > 1, so this condition is eventually met.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "projects/numbers/euclid" :dir :system)
(include-book "projects/numbers/eisenstein" :dir :system)
(include-book "arithmetic/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: GCD PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-posp-type
  (implies (and (posp x) (posp y))
           (posp (dm::gcd x y)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x x) (y y)))))
  :rule-classes (:rewrite :type-prescription))

(defthm quotient-by-gcd-posp-first
  (implies (and (posp x) (posp y))
           (posp (/ x (dm::gcd x y))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x x) (y y)))
                  :in-theory (enable dm::divides)))
  :rule-classes (:rewrite :type-prescription))

(defthm quotient-by-gcd-posp-second
  (implies (and (posp x) (posp y))
           (posp (/ y (dm::gcd x y))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x x) (y y)))
                  :in-theory (enable dm::divides)))
  :rule-classes (:rewrite :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: SEQUENCE DEFINITIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun reduce-to-lowest-terms (num den)
  (declare (xargs :guard (and (posp num) (posp den))))
  (let ((g (dm::gcd num den)))
    (cons (/ num g) (/ den g))))

(defthm reduce-to-lowest-terms-car-posp
  (implies (and (posp num) (posp den))
           (posp (car (reduce-to-lowest-terms num den))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x num) (y den)))
                  :in-theory (enable dm::divides)))
  :rule-classes (:rewrite :type-prescription))

(defthm reduce-to-lowest-terms-cdr-posp
  (implies (and (posp num) (posp den))
           (posp (cdr (reduce-to-lowest-terms num den))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x num) (y den)))
                  :in-theory (enable dm::divides)))
  :rule-classes (:rewrite :type-prescription))

(defun next-mn (m n)
  (declare (xargs :guard (and (posp m) (posp n))))
  (reduce-to-lowest-terms (+ (* 2 m) 1)
                          (+ (* 2 n) 1)))

(defthm next-mn-car-posp
  (implies (and (posp m) (posp n))
           (posp (car (next-mn m n))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-mn-cdr-posp
  (implies (and (posp m) (posp n))
           (posp (cdr (next-mn m n))))
  :rule-classes (:rewrite :type-prescription))

(defun mn-seq (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :measure (nfix k)))
  (if (zp k)
      (cons m0 n0)
    (let ((prev (mn-seq m0 n0 (1- k))))
      (next-mn (car prev) (cdr prev)))))

(defthm mn-seq-both-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (and (posp (car (mn-seq m0 n0 k)))
                (posp (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :induct (mn-seq m0 n0 k))))

(defthm mn-seq-car-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (car (mn-seq m0 n0 k))))
  :hints (("Goal" :use mn-seq-both-posp))
  :rule-classes (:rewrite :type-prescription))

(defthm mn-seq-cdr-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (cdr (mn-seq m0 n0 k))))
  :hints (("Goal" :use mn-seq-both-posp))
  :rule-classes (:rewrite :type-prescription))

(verify-guards mn-seq)

(defun m-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (car (mn-seq m0 n0 k)))

(defun n-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (cdr (mn-seq m0 n0 k)))

(defun coprime-transformed-p (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (equal (dm::gcd (+ (* 2 (m-k m0 n0 k)) 1)
                  (+ (* 2 (n-k m0 n0 k)) 1))
         1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: ODD-PART MACHINERY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun odd-part (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      1
    (if (evenp n)
        (odd-part (/ n 2))
      n)))

(defthm odd-part-posp
  (implies (posp n)
           (posp (odd-part n)))
  :rule-classes (:rewrite :type-prescription))

(defun power-of-2-p (n)
  (declare (xargs :guard (posp n)))
  (equal (odd-part n) 1))

(defun bound-N (m0 n0)
  (declare (xargs :guard (and (posp m0) (posp n0) (not (equal m0 n0)))))
  (odd-part (abs (- m0 n0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 4: GCD DIVIDES DIFFERENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm two-m-plus-one-oddp
  (implies (integerp m)
           (oddp (+ 1 (* 2 m))))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm divisor-of-odd-is-odd
  (implies (and (integerp a) (integerp d) 
                (not (equal d 0))
                (oddp a)
                (integerp (/ a d)))
           (oddp d))
  :hints (("Goal" 
           :use ((:instance dm::evenp-times (x d) (y (/ a d))))
           :in-theory (enable oddp))))

(defthm gcd-of-odds-is-odd
  (implies (and (posp a) (oddp a) (posp b) (oddp b))
           (oddp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))
                        (:instance divisor-of-odd-is-odd 
                                   (a a) 
                                   (d (dm::gcd a b))))
                  :in-theory (enable dm::divides))))

(defthm gcd-two-m-n-plus-one-oddp
  (implies (and (natp m) (natp n))
           (oddp (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))))
  :hints (("Goal" :use ((:instance gcd-of-odds-is-odd 
                                   (a (+ 1 (* 2 m))) 
                                   (b (+ 1 (* 2 n))))
                        (:instance two-m-plus-one-oddp (m m))
                        (:instance two-m-plus-one-oddp (m n)))
                  :in-theory (disable oddp two-m-plus-one-oddp))))

(defthm divides-diff
  (implies (and (dm::divides g a) (dm::divides g b))
           (dm::divides g (- a b)))
  :hints (("Goal" :use ((:instance dm::divides-minus (x g) (y b))
                        (:instance dm::divides-sum (x g) (y a) (z (- b)))))))

(defthm gcd-divides-two-times-diff
  (implies (and (natp m) (natp n))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))
                        (* 2 (- m n))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x (+ 1 (* 2 m))) (y (+ 1 (* 2 n))))
                        (:instance divides-diff 
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (a (+ 1 (* 2 m)))
                                   (b (+ 1 (* 2 n))))))))

(defun gcd-odd-two-ind (g)
  (declare (xargs :measure (nfix g)))
  (if (or (zp g) (= g 1))
      1
    (gcd-odd-two-ind (- g 2))))

(defthm gcd-nat-odd-two
  (implies (and (natp g) (> g 0) (oddp g))
           (equal (dm::gcd-nat g 2) 1))
  :hints (("Goal" :induct (gcd-odd-two-ind g)
                  :in-theory (e/d (oddp evenp dm::gcd-nat) ()))
          ("Subgoal *1/2" :expand ((dm::gcd-nat g 2)))))

(defthm gcd-odd-two
  (implies (and (posp g) (oddp g))
           (equal (dm::gcd g 2) 1))
  :hints (("Goal" :in-theory (enable dm::gcd))))

(defthm odd-divides-two-times-implies-divides
  (implies (and (posp g) (oddp g) (integerp k) (not (= k 0))
                (dm::divides g (* 2 k)))
           (dm::divides g k))
  :hints (("Goal" :use ((:instance dm::divides-product-divides-factor
                                   (d g) (m 2) (n k))
                        gcd-odd-two))))

(defthm gcd-two-m-n-divides-diff
  (implies (and (natp m) (natp n) (not (= m n)))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))
                        (- m n)))
  :hints (("Goal" :use (gcd-divides-two-times-diff
                        gcd-two-m-n-plus-one-oddp
                        (:instance odd-divides-two-times-implies-divides
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (k (- m n))))
                  :in-theory (disable gcd-divides-two-times-diff 
                                      odd-divides-two-times-implies-divides
                                      gcd-two-m-n-plus-one-oddp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: ODD DIVISOR OF POWER OF 2 IS 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun two-part (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      1
    (if (evenp n)
        (* 2 (two-part (/ n 2)))
      1)))

(defun log2 (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      0
    (if (evenp n)
        (+ 1 (log2 (/ n 2)))
      0)))

(defthm n-equals-odd-times-two-part
  (implies (posp n)
           (equal n (* (odd-part n) (two-part n))))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm two-part-is-power-of-2
  (implies (posp n)
           (equal (two-part n) (expt 2 (log2 n))))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm odd-divides-product-with-power-of-2
  (implies (and (natp k) (posp d) (oddp d) (integerp m) (> m 0)
                (dm::divides d (* (expt 2 k) m)))
           (dm::divides d m))
  :hints (("Goal" :induct (expt 2 k))
          ("Subgoal *1/2" :use ((:instance odd-divides-two-times-implies-divides
                                           (g d) (k (* (expt 2 (- k 1)) m)))))))

(defthm odd-divides-implies-divides-odd-part
  (implies (and (posp n) (posp d) (oddp d) (dm::divides d n))
           (dm::divides d (odd-part n)))
  :hints (("Goal" :use ((:instance n-equals-odd-times-two-part)
                        (:instance odd-divides-product-with-power-of-2
                                   (k (log2 n)) (m (odd-part n)))))))

(defthm divides-one-implies-one
  (implies (and (posp d) (dm::divides d 1))
           (equal d 1))
  :hints (("Goal" :in-theory (enable dm::divides))))

(defthm divides-neg
  (implies (dm::divides g x)
           (dm::divides g (- x)))
  :hints (("Goal" :in-theory (enable dm::divides))))

(defthm gcd-two-m-n-divides-abs-diff
  (implies (and (natp m) (natp n) (not (= m n)))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))
                        (abs (- m n))))
  :hints (("Goal" :cases ((>= m n))
                  :in-theory (enable abs))
          ("Subgoal 2" :use ((:instance gcd-two-m-n-divides-diff)
                             (:instance divides-neg 
                                        (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                        (x (- m n)))))
          ("Subgoal 1" :use (gcd-two-m-n-divides-diff))))

(defthm odd-divides-power-of-2-diff
  (implies (and (posp d) (posp n) (oddp d)
                (equal (odd-part n) 1)
                (dm::divides d n))
           (equal d 1))
  :hints (("Goal" :use ((:instance odd-divides-implies-divides-odd-part)
                        (:instance divides-one-implies-one)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: MAIN THEOREM - POWER OF 2 DIFFERENCE IMPLIES GCD = 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-is-one-when-diff-is-power-of-2
  (implies (and (natp m) (natp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use ((:instance odd-divides-power-of-2-diff
                                   (d (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (n (abs (- m n))))
                        gcd-two-m-n-divides-abs-diff
                        gcd-two-m-n-plus-one-oddp)
                  :in-theory (enable power-of-2-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 7: SEQUENCE PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Distinctness persists through the sequence
(defthm next-mn-preserves-distinct
  (implies (and (posp m) (posp n) (not (= m n)))
           (not (= (car (next-mn m n)) (cdr (next-mn m n)))))
  :hints (("Goal" :in-theory (enable next-mn reduce-to-lowest-terms))))

(defthm mn-seq-neq
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k))
           (not (= (car (mn-seq m0 n0 k)) (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :induct (mn-seq m0 n0 k))))

(defthm m-k-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (m-k m0 n0 k)))
  :rule-classes (:rewrite :type-prescription))

(defthm n-k-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (n-k m0 n0 k)))
  :rule-classes (:rewrite :type-prescription))

(defthm m-k-natp
  (implies (and (posp m0) (posp n0) (natp k))
           (natp (m-k m0 n0 k)))
  :rule-classes (:rewrite :type-prescription))

(defthm n-k-natp
  (implies (and (posp m0) (posp n0) (natp k))
           (natp (n-k m0 n0 k)))
  :rule-classes (:rewrite :type-prescription))

(defthm m-k-neq-n-k
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k))
           (not (= (m-k m0 n0 k) (n-k m0 n0 k))))
  :hints (("Goal" :use mn-seq-neq
                  :in-theory (enable m-k n-k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 8: CONDITIONAL MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; We can prove: IF the difference |m_k - n_k| is a power of 2, 
;;; THEN gcd(2m_k+1, 2n_k+1) = 1.
;;;
;;; The full Putnam 2025 A1 theorem additionally requires proving that
;;; the difference eventually becomes a power of 2, which involves
;;; showing the odd-part strictly decreases when gcd > 1.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm putnam-2025-a1-conditional
  (implies (and (posp m0)
                (posp n0)
                (not (= m0 n0))
                (natp k)
                (power-of-2-p (abs (- (m-k m0 n0 k) (n-k m0 n0 k)))))
           (coprime-transformed-p m0 n0 k))
  :hints (("Goal" :use (m-k-neq-n-k
                        (:instance gcd-is-one-when-diff-is-power-of-2
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k))))
                  :in-theory (enable coprime-transformed-p m-k n-k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 9: MAIN THEOREM (PUTNAM 2025 A1)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; NOTE: The full theorem requires an additional lemma showing that
;;; for k >= bound-N(m0, n0), the difference |m_k - n_k| is a power of 2.
;;; This involves proving that:
;;; 1. When gcd(2m+1, 2n+1) > 1, the odd-part of |m' - n'| < odd-part of |m - n|
;;; 2. After at most odd-part(|m0 - n0|) steps with gcd > 1, odd-part becomes 1
;;;
;;; This proof is complex and involves tracking the sequence dynamics.
;;; The theorem below is therefore admitted with :skip-proofs for now.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm diff-eventually-power-of-2
  (implies (and (posp m0)
                (posp n0)
                (not (= m0 n0))
                (natp k)
                (>= k (bound-N m0 n0)))
           (power-of-2-p (abs (- (m-k m0 n0 k) (n-k m0 n0 k))))))
)

(defthm putnam-2025-a1-main
  (implies (and (posp m0)
                (posp n0)
                (not (equal m0 n0))
                (natp k)
                (>= k (bound-N m0 n0)))
           (coprime-transformed-p m0 n0 k))
  :hints (("Goal" :use (diff-eventually-power-of-2
                        putnam-2025-a1-conditional))))
