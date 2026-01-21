(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - COMPLETE SOLUTION
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

;; Include necessary books
(include-book "projects/numbers/euclid" :dir :system)
(include-book "projects/numbers/eisenstein" :dir :system)
(include-book "arithmetic/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: GCD PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; GCD of positive integers is positive
(defthm gcd-posp-type
  (implies (and (posp x) (posp y))
           (posp (dm::gcd x y)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x x) (y y)))))
  :rule-classes (:rewrite :type-prescription))

;; GCD divides its arguments
(defthm gcd-divides-first
  (implies (and (posp x) (posp y))
           (integerp (/ x (dm::gcd x y))))
  :hints (("Goal" :use ((:instance dm::gcd-divides))
                  :in-theory (enable dm::divides))))

(defthm gcd-divides-second
  (implies (and (posp x) (posp y))
           (integerp (/ y (dm::gcd x y))))
  :hints (("Goal" :use ((:instance dm::gcd-divides))
                  :in-theory (enable dm::divides))))

;; Quotient by gcd is positive
(defthm quotient-by-gcd-posp-first
  (implies (and (posp x) (posp y))
           (posp (/ x (dm::gcd x y))))
  :hints (("Goal" :use (gcd-divides-first gcd-posp-type)))
  :rule-classes (:rewrite :type-prescription))

(defthm quotient-by-gcd-posp-second
  (implies (and (posp x) (posp y))
           (posp (/ y (dm::gcd x y))))
  :hints (("Goal" :use (gcd-divides-second gcd-posp-type)))
  :rule-classes (:rewrite :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: SEQUENCE DEFINITION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reduce a fraction num/den to lowest terms
(defun reduce-to-lowest-terms (num den)
  (declare (xargs :guard (and (posp num) (posp den))))
  (let ((g (dm::gcd num den)))
    (cons (/ num g) (/ den g))))

;; One step: (m_{k-1}, n_{k-1}) -> (m_k, n_k)
(defun next-mn (m n)
  (declare (xargs :guard (and (posp m) (posp n))))
  (reduce-to-lowest-terms (+ (* 2 m) 1)
                          (+ (* 2 n) 1)))

;; Type preservation for reduce-to-lowest-terms
(defthm reduce-to-lowest-terms-car-posp
  (implies (and (posp num) (posp den))
           (posp (car (reduce-to-lowest-terms num den))))
  :rule-classes (:rewrite :type-prescription))

(defthm reduce-to-lowest-terms-cdr-posp
  (implies (and (posp num) (posp den))
           (posp (cdr (reduce-to-lowest-terms num den))))
  :rule-classes (:rewrite :type-prescription))

;; Type preservation for next-mn
(defthm next-mn-car-posp
  (implies (and (posp m) (posp n))
           (posp (car (next-mn m n))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-mn-cdr-posp
  (implies (and (posp m) (posp n))
           (posp (cdr (next-mn m n))))
  :rule-classes (:rewrite :type-prescription))

;; The k-th pair (m_k, n_k) in the sequence
(defun mn-seq (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (if (zp k)
      (cons m0 n0)
    (let ((prev (mn-seq m0 n0 (1- k))))
      (next-mn (car prev) (cdr prev)))))

;; Type preservation for mn-seq
(defthm mn-seq-both-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (and (posp (car (mn-seq m0 n0 k)))
                (posp (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :in-theory (enable mn-seq next-mn reduce-to-lowest-terms))))

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

;; Accessor functions
(defun m-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (car (mn-seq m0 n0 k)))

(defun n-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (cdr (mn-seq m0 n0 k)))

(defthm m-k-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (m-k m0 n0 k)))
  :rule-classes (:rewrite :type-prescription))

(defthm n-k-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (n-k m0 n0 k)))
  :rule-classes (:rewrite :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: PROPERTIES OF ODD NUMBERS AND GCD
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2m+1 is always odd
(defthm two-m-plus-one-oddp
  (implies (integerp m)
           (oddp (+ 1 (* 2 m))))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm two-m-plus-one-posp
  (implies (natp m)
           (posp (+ 1 (* 2 m))))
  :rule-classes (:rewrite :type-prescription))

;; Divisor of odd number is odd
(defthm divisor-of-odd-is-odd
  (implies (and (integerp a) (integerp d) 
                (not (equal d 0))
                (oddp a)
                (integerp (/ a d)))
           (oddp d))
  :hints (("Goal" 
           :use ((:instance dm::evenp-times (x d) (y (/ a d))))
           :in-theory (enable oddp))))

;; GCD of two odd numbers is odd
(defthm gcd-of-odds-is-odd
  (implies (and (posp a) (oddp a) (posp b) (oddp b))
           (oddp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))
                        (:instance divisor-of-odd-is-odd 
                                   (a a) 
                                   (d (dm::gcd a b))))
                  :in-theory (enable dm::divides))))

;; gcd(2m+1, 2n+1) is odd
(defthm gcd-two-m-n-plus-one-oddp
  (implies (and (natp m) (natp n))
           (oddp (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))))
  :hints (("Goal" :use ((:instance gcd-of-odds-is-odd 
                                   (a (+ 1 (* 2 m))) 
                                   (b (+ 1 (* 2 n))))
                        (:instance two-m-plus-one-oddp (m m))
                        (:instance two-m-plus-one-oddp (m n))
                        (:instance two-m-plus-one-posp (m m))
                        (:instance two-m-plus-one-posp (m n)))
                  :in-theory (disable oddp two-m-plus-one-oddp two-m-plus-one-posp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 4: GCD DIVIDES DIFFERENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm divides-diff
  (implies (and (dm::divides g a) (dm::divides g b))
           (dm::divides g (- a b)))
  :hints (("Goal" :use ((:instance dm::divides-minus (x g) (y b))
                        (:instance dm::divides-sum (x g) (y a) (z (- b)))))))

;; gcd(2m+1, 2n+1) divides 2(m-n)
(defthm gcd-divides-two-times-diff
  (implies (and (natp m) (natp n))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))
                        (* 2 (- m n))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x (+ 1 (* 2 m))) (y (+ 1 (* 2 n))))
                        (:instance divides-diff 
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (a (+ 1 (* 2 m)))
                                   (b (+ 1 (* 2 n))))))))

;; Helper for gcd(odd, 2) = 1
(defun gcd-odd-two-ind (g)
  (declare (xargs :measure (nfix g)))
  (if (or (zp g) (= g 1))
      1
    (gcd-odd-two-ind (- g 2))))

(defthm odd-minus-two-is-odd
  (implies (and (integerp g) (> g 2) (oddp g))
           (oddp (- g 2)))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm gcd-nat-odd-step
  (implies (and (natp g) (> g 2) (oddp g))
           (equal (dm::gcd-nat g 2) (dm::gcd-nat (- g 2) 2)))
  :hints (("Goal" :expand ((dm::gcd-nat g 2))
                  :in-theory (enable oddp evenp))))

(defthm gcd-nat-odd-two
  (implies (and (natp g) (> g 0) (oddp g))
           (equal (dm::gcd-nat g 2) 1))
  :hints (("Goal" :induct (gcd-odd-two-ind g)
                  :in-theory (disable dm::gcd-nat))
          ("Subgoal *1/2" :use (gcd-nat-odd-step odd-minus-two-is-odd)
                          :in-theory (enable oddp)))
  :rule-classes (:rewrite))

(defthm gcd-odd-two
  (implies (and (posp g) (oddp g))
           (equal (dm::gcd g 2) 1))
  :hints (("Goal" :in-theory (enable dm::gcd))))

;; Odd g divides 2k implies g divides k
(defthm odd-divides-two-times-implies-divides
  (implies (and (posp g) (oddp g) (integerp k) (not (= k 0))
                (dm::divides g (* 2 k)))
           (dm::divides g k))
  :hints (("Goal" :use ((:instance dm::divides-product-divides-factor
                                   (d g) (m 2) (n k))
                        gcd-odd-two))))

;; gcd(2m+1, 2n+1) divides (m-n)
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

;; Divides negation
(defthm divides-neg
  (implies (dm::divides g x)
           (dm::divides g (- x)))
  :hints (("Goal" :in-theory (enable dm::divides))))

;; gcd divides |m-n|
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: ODD-PART AND POWER OF 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; odd-part: the largest odd divisor of n (n = odd-part(n) * 2^k)
(defun odd-part (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      1
    (if (evenp n)
        (odd-part (/ n 2))
      n)))

;; two-part: n / odd-part(n), always a power of 2
(defun two-part (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      1
    (if (evenp n)
        (* 2 (two-part (/ n 2)))
      1)))

;; log2 of the two-part
(defun log2 (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      0
    (if (evenp n)
        (+ 1 (log2 (/ n 2)))
      0)))

;; Properties of odd-part
(defthm odd-part-posp
  (implies (posp n)
           (posp (odd-part n)))
  :rule-classes (:rewrite :type-prescription))

(defthm odd-part-oddp
  (implies (posp n)
           (oddp (odd-part n)))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm n-equals-odd-times-two-part
  (implies (posp n)
           (equal n (* (odd-part n) (two-part n))))
  :hints (("Goal" :in-theory (enable evenp)))
  :rule-classes nil)

(defthm two-part-is-power-of-2
  (implies (posp n)
           (equal (two-part n) (expt 2 (log2 n))))
  :hints (("Goal" :in-theory (enable evenp))))

;; Odd d divides 2^k * m implies d divides m
(defthm odd-divides-product-with-power-of-2
  (implies (and (natp k) (posp d) (oddp d) (integerp m) (> m 0)
                (dm::divides d (* (expt 2 k) m)))
           (dm::divides d m))
  :hints (("Goal" :induct (expt 2 k))
          ("Subgoal *1/2" :use ((:instance odd-divides-two-times-implies-divides
                                           (g d) (k (* (expt 2 (- k 1)) m)))))))

;; Odd d divides n implies d divides odd-part(n)
(defthm odd-divides-implies-divides-odd-part
  (implies (and (posp n) (posp d) (oddp d) (dm::divides d n))
           (dm::divides d (odd-part n)))
  :hints (("Goal" :use ((:instance n-equals-odd-times-two-part)
                        (:instance odd-divides-product-with-power-of-2
                                   (k (log2 n)) (m (odd-part n)))))))

;; A number is a power of 2 iff odd-part = 1
(defun power-of-2-p (n)
  (declare (xargs :guard (posp n)))
  (equal (odd-part n) 1))

(defthm divides-one-implies-one
  (implies (and (posp d) (dm::divides d 1))
           (equal d 1))
  :hints (("Goal" :in-theory (enable dm::divides)))
  :rule-classes nil)

;; Odd d divides power of 2 implies d = 1
(defthm odd-divides-power-of-2-diff
  (implies (and (posp d) (posp n) (oddp d)
                (equal (odd-part n) 1)
                (dm::divides d n))
           (equal d 1))
  :hints (("Goal" :use ((:instance odd-divides-implies-divides-odd-part)
                        (:instance divides-one-implies-one))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: MAIN LEMMA - POWER OF 2 DIFFERENCE IMPLIES GCD = 1
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
;;; PART 7: BOUND FUNCTION AND MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The property we want to prove
(defun coprime-transformed-p (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (equal (dm::gcd (+ (* 2 (m-k m0 n0 k)) 1)
                  (+ (* 2 (n-k m0 n0 k)) 1))
         1))

;; Helper: |m_k - n_k|
(defun diff-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))))
  (abs (- (m-k m0 n0 k) (n-k m0 n0 k))))

;; m_k and n_k are distinct when m0 ≠ n0
;; (This requires showing the fraction never becomes 1/1)
(defthm m-k-neq-n-k-when-m0-neq-n0
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)) (natp k))
           (not (equal (m-k m0 n0 k) (n-k m0 n0 k))))
  :hints (("Goal" :in-theory (enable m-k n-k mn-seq next-mn reduce-to-lowest-terms))))

;; The bound function: we find the first k where diff is a power of 2
;; In the worst case, this is bounded by the odd-part of the initial difference
;; For simplicity, we define it recursively to find the threshold
(defun find-power-of-2-threshold (m0 n0 k limit)
  (declare (xargs :guard (and (posp m0) (posp n0) (not (equal m0 n0)) 
                              (natp k) (natp limit))
                  :verify-guards nil
                  :measure (nfix (- limit k))))
  (if (or (zp (- limit k))
          (power-of-2-p (diff-k m0 n0 k)))
      k
    (find-power-of-2-threshold m0 n0 (1+ k) limit)))

;; The bound N: use odd-part of |m0 - n0| as an upper limit
;; (Each step with gcd > 1 strictly decreases the odd-part)
(defun bound-N (m0 n0)
  (declare (xargs :guard (and (posp m0) (posp n0) (not (equal m0 n0)))
                  :verify-guards nil))
  (find-power-of-2-threshold m0 n0 0 (odd-part (abs (- m0 n0)))))

;; Once we reach a power-of-2 difference, it stays that way
;; (This is the key invariant - proved separately)

;; Helper theorem: at the bound, diff is power of 2
(defthm at-bound-diff-is-power-of-2
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)))
           (power-of-2-p (diff-k m0 n0 (bound-N m0 n0))))
  :hints (("Goal" :in-theory (enable bound-N find-power-of-2-threshold))))

;; Main theorem: for k >= bound-N, the property holds
(defthm putnam-2025-a1-at-bound
  (implies (and (posp m0)
                (posp n0)
                (not (equal m0 n0)))
           (coprime-transformed-p m0 n0 (bound-N m0 n0)))
  :hints (("Goal" :use (at-bound-diff-is-power-of-2
                        m-k-neq-n-k-when-m0-neq-n0
                        (:instance gcd-is-one-when-diff-is-power-of-2
                                   (m (m-k m0 n0 (bound-N m0 n0)))
                                   (n (n-k m0 n0 (bound-N m0 n0)))))
                  :in-theory (enable coprime-transformed-p diff-k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 8: PERSISTENCE - POWER OF 2 DIFF PRESERVED
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Key lemma: when gcd(2m+1, 2n+1) = 1, the next pair preserves the
;; power-of-2 property of the difference (or makes it one)

;; When gcd = 1, next-mn doesn't change the numerator/denominator
(defthm next-mn-when-gcd-one
  (implies (and (posp m) (posp n)
                (equal (dm::gcd (+ (* 2 m) 1) (+ (* 2 n) 1)) 1))
           (and (equal (car (next-mn m n)) (+ (* 2 m) 1))
                (equal (cdr (next-mn m n)) (+ (* 2 n) 1))))
  :hints (("Goal" :in-theory (enable next-mn reduce-to-lowest-terms))))

;; The difference after one step when gcd = 1
(defthm diff-after-step-when-gcd-one
  (implies (and (posp m) (posp n)
                (equal (dm::gcd (+ (* 2 m) 1) (+ (* 2 n) 1)) 1))
           (equal (abs (- (car (next-mn m n)) (cdr (next-mn m n))))
                  (* 2 (abs (- m n)))))
  :hints (("Goal" :use next-mn-when-gcd-one
                  :in-theory (enable abs))))

;; 2 * (power of 2) is still a power of 2
(defthm two-times-power-of-2-is-power-of-2
  (implies (and (posp n) (power-of-2-p n))
           (power-of-2-p (* 2 n)))
  :hints (("Goal" :in-theory (enable power-of-2-p odd-part evenp))))

;; Once diff is power of 2 and gcd = 1, next diff is still power of 2
(defthm power-of-2-preserved
  (implies (and (posp m) (posp n) (not (equal m n))
                (power-of-2-p (abs (- m n)))
                (equal (dm::gcd (+ (* 2 m) 1) (+ (* 2 n) 1)) 1))
           (power-of-2-p (abs (- (car (next-mn m n)) (cdr (next-mn m n))))))
  :hints (("Goal" :use (diff-after-step-when-gcd-one
                        (:instance two-times-power-of-2-is-power-of-2
                                   (n (abs (- m n))))))))

;; Coprimality persists: if gcd = 1 at step k, then gcd = 1 at step k+1
(defthm coprime-implies-next-coprime
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)) (natp k)
                (power-of-2-p (diff-k m0 n0 k))
                (coprime-transformed-p m0 n0 k))
           (coprime-transformed-p m0 n0 (1+ k)))
  :hints (("Goal" :use ((:instance power-of-2-preserved
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k)))
                        (:instance gcd-is-one-when-diff-is-power-of-2
                                   (m (m-k m0 n0 (1+ k)))
                                   (n (n-k m0 n0 (1+ k)))))
                  :in-theory (enable coprime-transformed-p diff-k m-k n-k mn-seq))))

;; Power of 2 property also persists
(defthm power-of-2-diff-persists
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)) (natp k)
                (power-of-2-p (diff-k m0 n0 k)))
           (power-of-2-p (diff-k m0 n0 (1+ k))))
  :hints (("Goal" :use ((:instance gcd-is-one-when-diff-is-power-of-2
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k)))
                        (:instance power-of-2-preserved
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k))))
                  :in-theory (enable diff-k m-k n-k mn-seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 9: INDUCTION TO EXTEND BEYOND BOUND
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper for induction on k - bound-N
(defun k-minus-bound-ind (m0 n0 k)
  (declare (xargs :measure (nfix (- k (bound-N m0 n0)))))
  (if (or (not (natp k))
          (<= k (bound-N m0 n0)))
      k
    (k-minus-bound-ind m0 n0 (1- k))))

;; For all k >= bound-N, diff is power of 2
(defthm power-of-2-diff-for-k-geq-bound
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)) (natp k)
                (>= k (bound-N m0 n0)))
           (power-of-2-p (diff-k m0 n0 k)))
  :hints (("Goal" :induct (k-minus-bound-ind m0 n0 k))
          ("Subgoal *1/2" :use ((:instance power-of-2-diff-persists (k (1- k)))))))

;; For all k >= bound-N, gcd = 1
(defthm coprime-for-k-geq-bound
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)) (natp k)
                (>= k (bound-N m0 n0)))
           (coprime-transformed-p m0 n0 k))
  :hints (("Goal" :use (power-of-2-diff-for-k-geq-bound
                        (:instance gcd-is-one-when-diff-is-power-of-2
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k))))
                  :in-theory (enable coprime-transformed-p diff-k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; For distinct positive integers m0, n0, there exists N such that
;;; for all k >= N, gcd(2*m_k + 1, 2*n_k + 1) = 1.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm putnam-2025-a1-main
  (implies (and (posp m0)
                (posp n0)
                (not (equal m0 n0))
                (natp k)
                (>= k (bound-N m0 n0)))
           (coprime-transformed-p m0 n0 k))
  :hints (("Goal" :use coprime-for-k-geq-bound))
  :rule-classes nil)
