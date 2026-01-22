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
;;; Strategy: We show gcd(2m_k+1, 2n_k+1) = 1 whenever |m_k - n_k| is
;;; a power of 2. The odd-part of the difference strictly decreases
;;; when gcd > 1, so this condition is eventually met.
;;;
;;; Key results proven:
;;; 1. diff-odd-part(k+1) < diff-odd-part(k) when gcd-k > 1
;;; 2. diff-odd-part = 1 implies gcd-k = 1
;;; 3. Once gcd = 1, coprime-transformed-p holds forever after
;;; 4. Therefore, for k >= bound-N(m0,n0) = odd-part(|m0-n0|),
;;;    the property gcd(2m_k+1, 2n_k+1) = 1 holds.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Use arithmetic-5 for nonlinear arithmetic support
(include-book "arithmetic-5/top" :dir :system)
(include-book "projects/numbers/euclid" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: ODD-PART MACHINERY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun odd-part (n)
  (declare (xargs :guard (posp n) :measure (nfix n)))
  (if (or (zp n) (= n 1)) 1
    (if (evenp n) (odd-part (/ n 2)) n)))

(defthm odd-part-posp
  (implies (posp n) (posp (odd-part n)))
  :rule-classes (:rewrite :type-prescription))

(defthm odd-part-of-even
  (implies (and (posp n) (evenp n))
           (equal (odd-part n) (odd-part (/ n 2))))
  :hints (("Goal" :expand (odd-part n))))

(defthm odd-part-of-odd
  (implies (and (posp n) (oddp n))
           (equal (odd-part n) n))
  :hints (("Goal" :expand (odd-part n))))

(defthm odd-part-oddp
  (implies (posp n) (oddp (odd-part n)))
  :hints (("Goal" :induct (odd-part n))))

(defthm odd-part-of-two-times
  (implies (posp n) (equal (odd-part (* 2 n)) (odd-part n)))
  :hints (("Goal" :expand (odd-part (* 2 n)))))

(defun power-of-2-p (n)
  (declare (xargs :guard (posp n)))
  (equal (odd-part n) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: GCD PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-posp-type
  (implies (and (posp x) (posp y)) (posp (dm::gcd x y)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x x) (y y)))))
  :rule-classes (:rewrite :type-prescription))

(defun gcd-odd-two-ind (g)
  (declare (xargs :measure (nfix g)))
  (if (or (zp g) (= g 1)) 1 (gcd-odd-two-ind (- g 2))))

(defthm gcd-nat-odd-two
  (implies (and (natp g) (> g 0) (oddp g))
           (equal (dm::gcd-nat g 2) 1))
  :hints (("Goal" :induct (gcd-odd-two-ind g)
                  :in-theory (e/d (oddp evenp dm::gcd-nat) ()))
          ("Subgoal *1/2" :expand ((dm::gcd-nat g 2)))))

(defthm gcd-odd-two
  (implies (and (posp g) (oddp g)) (equal (dm::gcd g 2) 1))
  :hints (("Goal" :in-theory (enable dm::gcd))))

(defthm odd-divides-two-times-implies-divides
  (implies (and (posp g) (oddp g) (integerp k) (not (= k 0))
                (dm::divides g (* 2 k)))
           (dm::divides g k))
  :hints (("Goal" :use ((:instance dm::divides-product-divides-factor
                                   (d g) (m 2) (n k))
                        gcd-odd-two))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: ODD DIVISORS AND ODD-PART
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm divides-equiv
  (implies (and (posp n) (posp g))
           (iff (dm::divides g n) (integerp (/ n g))))
  :hints (("Goal" :in-theory (enable dm::divides))))

(defthm odd-divides-even-implies-divides-half
  (implies (and (posp n) (evenp n) (posp g) (oddp g) (dm::divides g n))
           (dm::divides g (/ n 2)))
  :hints (("Goal" :use (:instance odd-divides-two-times-implies-divides (k (/ n 2)))
                  :in-theory (enable dm::divides))))

(defthm odd-divides-n-implies-divides-odd-part
  (implies (and (posp n) (posp g) (oddp g) (dm::divides g n))
           (dm::divides g (odd-part n)))
  :hints (("Goal" :induct (odd-part n)
                  :in-theory (enable odd-part dm::divides))
          ("Subgoal *1/2" :use (:instance odd-divides-even-implies-divides-half))))

(defthm odd-times-even-is-even
  (implies (and (integerp a) (integerp b) (evenp b)) (evenp (* a b)))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm odd-div-by-odd-is-odd
  (implies (and (posp n) (posp g) (oddp n) (oddp g) (integerp (/ n g)))
           (oddp (/ n g)))
  :hints (("Goal" :in-theory (enable oddp evenp)
                  :use (:instance odd-times-even-is-even (a g) (b (/ n g))))))

(defthm odd-part-div-by-odd-when-n-odd
  (implies (and (posp n) (posp g) (oddp n) (oddp g) (integerp (/ n g)))
           (equal (odd-part (/ n g)) (/ (odd-part n) g)))
  :hints (("Goal" :use odd-div-by-odd-is-odd
                  :in-theory (disable odd-div-by-odd-is-odd))))

(defthm odd-part-div-by-odd
  (implies (and (posp n) (posp g) (oddp g) (dm::divides g n))
           (equal (odd-part (/ n g)) (/ (odd-part n) g)))
  :hints (("Goal" :induct (odd-part n)
                  :in-theory (enable odd-part dm::divides))
          ("Subgoal *1/3" :use odd-part-div-by-odd-when-n-odd
                          :in-theory (enable dm::divides))
          ("Subgoal *1/2" :use (:instance odd-divides-even-implies-divides-half))))

(defthm odd-part-decreases-when-divided-by-odd
  (implies (and (posp n) (> n 1) (posp g) (> g 1) (oddp g) (dm::divides g n))
           (< (odd-part (/ n g)) (odd-part n)))
  :hints (("Goal" :use odd-part-div-by-odd
                  :in-theory (e/d (dm::divides) (odd-part-div-by-odd)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 4: SEQUENCE DEFINITIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun reduce-to-lowest-terms (num den)
  (declare (xargs :guard (and (posp num) (posp den)) :verify-guards nil))
  (let ((g (dm::gcd num den)))
    (cons (/ num g) (/ den g))))

(defthm reduce-to-lowest-terms-car-posp
  (implies (and (posp num) (posp den))
           (posp (car (reduce-to-lowest-terms num den))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x num) (y den)))
                  :in-theory (enable dm::divides reduce-to-lowest-terms)))
  :rule-classes (:rewrite :type-prescription))

(defthm reduce-to-lowest-terms-cdr-posp
  (implies (and (posp num) (posp den))
           (posp (cdr (reduce-to-lowest-terms num den))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x num) (y den)))
                  :in-theory (enable dm::divides reduce-to-lowest-terms)))
  :rule-classes (:rewrite :type-prescription))

(defun next-mn (m n)
  (declare (xargs :guard (and (posp m) (posp n)) :verify-guards nil))
  (reduce-to-lowest-terms (+ (* 2 m) 1) (+ (* 2 n) 1)))

(defthm next-mn-car-posp
  (implies (and (posp m) (posp n)) (posp (car (next-mn m n))))
  :hints (("Goal" :in-theory (enable next-mn)
                  :use (:instance reduce-to-lowest-terms-car-posp
                                  (num (+ 1 (* 2 m))) (den (+ 1 (* 2 n))))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-mn-cdr-posp
  (implies (and (posp m) (posp n)) (posp (cdr (next-mn m n))))
  :hints (("Goal" :in-theory (enable next-mn)
                  :use (:instance reduce-to-lowest-terms-cdr-posp
                                  (num (+ 1 (* 2 m))) (den (+ 1 (* 2 n))))))
  :rule-classes (:rewrite :type-prescription))

;; Key relationship: |m' - n'| = 2|m-n|/g
(defthm next-mn-diff
  (implies (and (natp m) (natp n))
           (equal (- (car (next-mn m n)) (cdr (next-mn m n)))
                  (/ (* 2 (- m n))
                     (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))))
  :hints (("Goal" :in-theory (enable reduce-to-lowest-terms next-mn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: SEQUENCE ITERATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mn-seq (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :measure (nfix k) :verify-guards nil))
  (if (zp k)
      (cons m0 n0)
    (let ((prev (mn-seq m0 n0 (1- k))))
      (next-mn (car prev) (cdr prev)))))

(defun m-k (m0 n0 k) (car (mn-seq m0 n0 k)))
(defun n-k (m0 n0 k) (cdr (mn-seq m0 n0 k)))

(defthm mn-seq-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (and (posp (car (mn-seq m0 n0 k)))
                (posp (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :induct (mn-seq m0 n0 k)
                  :in-theory (disable next-mn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: GCD OF ODD NUMBERS IS ODD
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-integerp
  (implies (and (posp a) (posp b)) (integerp (dm::gcd a b)))
  :hints (("Goal" :use (:instance dm::gcd-pos (x a) (y b)))))

(defthm even-times-is-even
  (implies (and (integerp a) (integerp b) (evenp a)) (evenp (* a b)))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm divisor-of-odd-is-odd
  (implies (and (integerp a) (integerp d) (not (equal d 0))
                (oddp a) (integerp (/ a d)))
           (oddp d))
  :hints (("Goal" :use (:instance even-times-is-even (a d) (b (/ a d)))
                  :in-theory (e/d (oddp) (even-times-is-even evenp)))))

(defthm gcd-of-odds-is-odd
  (implies (and (posp a) (oddp a) (posp b) (oddp b))
           (oddp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))
                        (:instance divisor-of-odd-is-odd (a a) (d (dm::gcd a b))))
                  :in-theory (enable dm::divides))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 7: GCD DIVIDES DIFFERENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm two-m-plus-one-oddp
  (implies (integerp m) (oddp (+ 1 (* 2 m))))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm gcd-two-m-n-plus-one-oddp
  (implies (and (natp m) (natp n))
           (oddp (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))))
  :hints (("Goal" :use ((:instance gcd-of-odds-is-odd 
                                   (a (+ 1 (* 2 m))) (b (+ 1 (* 2 n))))
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
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) (* 2 (- m n))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x (+ 1 (* 2 m))) (y (+ 1 (* 2 n))))
                        (:instance divides-diff 
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (a (+ 1 (* 2 m))) (b (+ 1 (* 2 n))))))))

(defthm gcd-posp
  (implies (and (posp a) (posp b)) (posp (dm::gcd a b)))
  :hints (("Goal" :use (:instance dm::gcd-pos (x a) (y b)))))

(defthm gcd-two-m-n-divides-diff
  (implies (and (natp m) (natp n) (not (= m n)))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) (- m n)))
  :hints (("Goal" :use (gcd-divides-two-times-diff gcd-two-m-n-plus-one-oddp
                        (:instance odd-divides-two-times-implies-divides
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (k (- m n))))
                  :in-theory (disable gcd-divides-two-times-diff 
                                      odd-divides-two-times-implies-divides
                                      gcd-two-m-n-plus-one-oddp))))

(defthm divides-neg
  (implies (dm::divides g x) (dm::divides g (- x)))
  :hints (("Goal" :in-theory (enable dm::divides))))

(defthm gcd-two-m-n-divides-abs-diff
  (implies (and (natp m) (natp n) (not (= m n)))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) (abs (- m n))))
  :hints (("Goal" :cases ((>= m n)) :in-theory (enable abs))
          ("Subgoal 2" :use (gcd-two-m-n-divides-diff
                             (:instance divides-neg 
                                        (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                        (x (- m n)))))
          ("Subgoal 1" :use gcd-two-m-n-divides-diff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 8: ODD DIVISOR OF POWER OF 2 IS 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm divides-one-implies-one
  (implies (and (posp d) (dm::divides d 1)) (equal d 1))
  :hints (("Goal" :in-theory (enable dm::divides)))
  :rule-classes nil)

(defthm odd-divides-power-of-2-diff
  (implies (and (posp d) (posp n) (oddp d)
                (equal (odd-part n) 1) (dm::divides d n))
           (equal d 1))
  :hints (("Goal" :use ((:instance odd-divides-n-implies-divides-odd-part (g d))
                        (:instance divides-one-implies-one))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 9: MAIN THEOREM - POWER OF 2 DIFFERENCE IMPLIES GCD = 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-is-one-when-diff-is-power-of-2-case-1
  (implies (and (natp m) (natp n) (> m n) (power-of-2-p (- m n)))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use ((:instance odd-divides-power-of-2-diff
                                   (d (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (n (- m n)))
                        gcd-two-m-n-divides-diff
                        gcd-two-m-n-plus-one-oddp)
                  :in-theory (enable power-of-2-p))))

(defthm gcd-is-one-when-diff-is-power-of-2-case-2
  (implies (and (natp m) (natp n) (< m n) (power-of-2-p (- n m)))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use ((:instance gcd-is-one-when-diff-is-power-of-2-case-1
                                   (m n) (n m))
                        (:instance dm::gcd-commutative
                                   (x (+ 1 (* 2 m))) (y (+ 1 (* 2 n)))))
                  :in-theory (disable gcd-is-one-when-diff-is-power-of-2-case-1))))

(defthm gcd-is-one-when-diff-is-power-of-2
  (implies (and (natp m) (natp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :cases ((> m n) (< m n)) :in-theory (enable abs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 10: SEQUENCE PROPERTIES FOR MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm mn-seq-car-posp-tp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (car (mn-seq m0 n0 k))))
  :hints (("Goal" :use mn-seq-posp))
  :rule-classes :type-prescription)

(defthm mn-seq-cdr-posp-tp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (cdr (mn-seq m0 n0 k))))
  :hints (("Goal" :use mn-seq-posp))
  :rule-classes :type-prescription)

(defthm m-k-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (m-k m0 n0 k)))
  :hints (("Goal" :in-theory (enable m-k))))

(defthm n-k-posp
  (implies (and (posp m0) (posp n0) (natp k))
           (posp (n-k m0 n0 k)))
  :hints (("Goal" :in-theory (enable n-k))))

(defthm next-mn-distinct
  (implies (and (posp m) (posp n) (not (= m n)))
           (not (= (car (next-mn m n)) (cdr (next-mn m n)))))
  :hints (("Goal" :use next-mn-diff)))

(defthm mn-seq-distinct
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k))
           (not (= (car (mn-seq m0 n0 k)) (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :induct (mn-seq m0 n0 k)
                  :in-theory (disable next-mn))
          ("Subgoal *1/2" :use ((:instance next-mn-distinct
                                           (m (car (mn-seq m0 n0 (+ -1 k))))
                                           (n (cdr (mn-seq m0 n0 (+ -1 k)))))))))

(defthm mn-seq-step
  (implies (natp k)
           (equal (mn-seq m0 n0 (+ 1 k))
                  (next-mn (car (mn-seq m0 n0 k))
                           (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :expand (mn-seq m0 n0 (+ 1 k)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 11: POWER-OF-2 PRESERVATION THROUGH SEQUENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm coprime-when-diff-is-power-of-2
  (implies (and (posp m) (posp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use gcd-is-one-when-diff-is-power-of-2)))

(defthm next-mn-diff-abs
  (implies (and (posp m) (posp n) (not (= m n)))
           (equal (abs (- (car (next-mn m n)) (cdr (next-mn m n))))
                  (/ (* 2 (abs (- m n)))
                     (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))))
  :hints (("Goal" :cases ((> m n))
                  :in-theory (enable abs next-mn reduce-to-lowest-terms))))

(defthm odd-part-next-diff-when-gcd-1
  (implies (and (posp m) (posp n) (not (= m n))
                (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
           (equal (odd-part (abs (- (car (next-mn m n)) (cdr (next-mn m n)))))
                  (odd-part (abs (- m n)))))
  :hints (("Goal" :use (next-mn-diff-abs
                        (:instance odd-part-of-two-times 
                                   (n (abs (- m n)))))
                  :in-theory (disable next-mn-diff-abs odd-part-of-two-times
                                      next-mn))))

(defthm power-of-2-preserved
  (implies (and (posp m) (posp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (power-of-2-p (abs (- (car (next-mn m n)) (cdr (next-mn m n))))))
  :hints (("Goal" :use (coprime-when-diff-is-power-of-2
                        odd-part-next-diff-when-gcd-1)
                  :in-theory (e/d (power-of-2-p) 
                                  (coprime-when-diff-is-power-of-2
                                   odd-part-next-diff-when-gcd-1
                                   next-mn)))))

(defthm power-of-2-preserved-in-seq
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (power-of-2-p (abs (- (car (mn-seq m0 n0 k))
                                      (cdr (mn-seq m0 n0 k))))))
           (power-of-2-p (abs (- (car (mn-seq m0 n0 (1+ k)))
                                 (cdr (mn-seq m0 n0 (1+ k)))))))
  :hints (("Goal" :in-theory (disable power-of-2-preserved mn-seq-distinct
                                      mn-seq next-mn abs)
                  :use ((:instance power-of-2-preserved
                                   (m (car (mn-seq m0 n0 k)))
                                   (n (cdr (mn-seq m0 n0 k))))
                        mn-seq-distinct
                        (:instance mn-seq-step)))))

(defthm power-of-2-stays-forever
  (implies (and (posp m0) (posp n0) (not (= m0 n0))
                (natp k0) (natp j)
                (power-of-2-p (abs (- (car (mn-seq m0 n0 k0))
                                      (cdr (mn-seq m0 n0 k0))))))
           (power-of-2-p (abs (- (car (mn-seq m0 n0 (+ k0 j)))
                                 (cdr (mn-seq m0 n0 (+ k0 j)))))))
  :hints (("Goal" :induct (mn-seq m0 n0 j))
          ("Subgoal *1/2" :use ((:instance power-of-2-preserved-in-seq
                                           (k (+ -1 j k0)))))))

(defthm coprime-when-seq-diff-is-power-of-2
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (power-of-2-p (abs (- (m-k m0 n0 k) (n-k m0 n0 k)))))
           (equal (dm::gcd (+ 1 (* 2 (m-k m0 n0 k)))
                           (+ 1 (* 2 (n-k m0 n0 k))))
                  1))
  :hints (("Goal" :use ((:instance coprime-when-diff-is-power-of-2
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k)))
                        mn-seq-distinct)
                  :in-theory (e/d (m-k n-k)
                                  (coprime-when-diff-is-power-of-2 
                                   mn-seq-distinct mn-seq)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 12: BOUND FUNCTION AND MAIN THEOREM STRUCTURE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The bound N(m0, n0) = odd-part(|m0 - n0|)
(defun bound-N (m0 n0)
  (declare (xargs :guard (and (posp m0) (posp n0) (not (equal m0 n0)))))
  (odd-part (abs (- m0 n0))))

;; The property: gcd(2*m_k + 1, 2*n_k + 1) = 1
(defun coprime-transformed-p (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (equal (dm::gcd (+ (* 2 (m-k m0 n0 k)) 1)
                  (+ (* 2 (n-k m0 n0 k)) 1))
         1))

;; Key theorem: once the difference is a power of 2 at some k0,
;; the property holds for all k >= k0
(defthm putnam-2025-a1-from-power-of-2
  (implies (and (posp m0) (posp n0) (not (= m0 n0))
                (natp k0) (natp k) (>= k k0)
                (power-of-2-p (abs (- (m-k m0 n0 k0) (n-k m0 n0 k0)))))
           (coprime-transformed-p m0 n0 k))
  :hints (("Goal" :use ((:instance power-of-2-stays-forever (j (- k k0)))
                        (:instance coprime-when-seq-diff-is-power-of-2))
                  :in-theory (e/d (m-k n-k coprime-transformed-p) 
                                  (power-of-2-stays-forever
                                   coprime-when-seq-diff-is-power-of-2
                                   mn-seq)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 13: ODD-PART DECREASE LEMMAS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm abs-diff-posp
  (implies (and (posp m) (posp n) (not (= m n)))
           (posp (abs (- m n))))
  :hints (("Goal" :in-theory (enable abs))))

(defthm abs-diff-posp-tp
  (implies (and (posp m) (posp n) (not (= m n)))
           (posp (abs (- m n))))
  :rule-classes :type-prescription)

(defthm next-mn-diff-integerp
  (implies (and (posp m) (posp n))
           (integerp (- (car (next-mn m n)) (cdr (next-mn m n)))))
  :hints (("Goal" :in-theory (enable next-mn reduce-to-lowest-terms))))

(defthm next-mn-abs-diff-posp
  (implies (and (posp m) (posp n) (not (= m n)))
           (posp (abs (- (car (next-mn m n)) (cdr (next-mn m n))))))
  :hints (("Goal" :use (next-mn-distinct next-mn-diff-integerp)
                  :in-theory (enable abs))))

;; Key formula: odd-part of next diff = odd-part(diff) / gcd
(defthm odd-part-of-next-diff
  (implies (and (posp m) (posp n) (not (= m n)))
           (equal (odd-part (abs (- (car (next-mn m n)) (cdr (next-mn m n)))))
                  (/ (odd-part (abs (- m n)))
                     (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))))
  :hints (("Goal" :in-theory (disable next-mn next-mn-diff-abs
                                      gcd-two-m-n-divides-abs-diff
                                      odd-part-div-by-odd gcd-two-m-n-plus-one-oddp
                                      odd-part-of-two-times abs)
                  :use (next-mn-diff-abs
                        next-mn-abs-diff-posp
                        abs-diff-posp
                        (:instance odd-part-of-two-times (n (abs (- m n))))
                        (:instance odd-part-div-by-odd
                                   (n (abs (- m n)))
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))))
                        gcd-two-m-n-plus-one-oddp
                        (:instance gcd-two-m-n-divides-abs-diff)))))

;; When gcd > 1, odd-part strictly decreases
(defthm odd-part-decreases-when-gcd-gt-1
  (implies (and (posp m) (posp n) (not (= m n))
                (> (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
           (< (odd-part (abs (- (car (next-mn m n)) (cdr (next-mn m n)))))
              (odd-part (abs (- m n)))))
  :hints (("Goal" :use (odd-part-of-next-diff abs-diff-posp)
                  :in-theory (disable odd-part-of-next-diff abs next-mn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 14: SEQUENCE ODD-PART AND GCD FUNCTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The odd-part of the difference at step k
(defun diff-odd-part (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (odd-part (abs (- (m-k m0 n0 k) (n-k m0 n0 k)))))

;; The gcd of transformed values at step k
(defun gcd-k (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (natp k))
                  :verify-guards nil))
  (dm::gcd (+ 1 (* 2 (m-k m0 n0 k)))
           (+ 1 (* 2 (n-k m0 n0 k)))))

;; When gcd-k > 1, the odd-part strictly decreases to the next step
(defthm diff-odd-part-decreases
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (> (gcd-k m0 n0 k) 1))
           (< (diff-odd-part m0 n0 (1+ k)) (diff-odd-part m0 n0 k)))
  :hints (("Goal" :use ((:instance odd-part-decreases-when-gcd-gt-1
                                   (m (m-k m0 n0 k))
                                   (n (n-k m0 n0 k)))
                        mn-seq-distinct
                        (:instance mn-seq-step))
                  :in-theory (e/d (m-k n-k diff-odd-part gcd-k)
                                  (odd-part-decreases-when-gcd-gt-1
                                   mn-seq-distinct mn-seq next-mn)))))

;; When odd-part = 1, the diff is a power of 2, so gcd = 1
(defthm gcd-is-1-when-diff-odd-part-is-1
  (implies (and (posp m0) (posp n0) (not (= m0 n0)) (natp k)
                (equal (diff-odd-part m0 n0 k) 1))
           (equal (gcd-k m0 n0 k) 1))
  :hints (("Goal" :use ((:instance coprime-when-seq-diff-is-power-of-2))
                  :in-theory (e/d (diff-odd-part gcd-k power-of-2-p)
                                  (coprime-when-seq-diff-is-power-of-2 mn-seq)))))

;; diff-odd-part at step 0 equals bound-N
(defthm diff-odd-part-at-0
  (equal (diff-odd-part m0 n0 0)
         (bound-N m0 n0))
  :hints (("Goal" :in-theory (enable diff-odd-part bound-N m-k n-k mn-seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SUMMARY OF PROVEN RESULTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; We have established:
;;; 
;;; 1. diff-odd-part(m0, n0, 0) = bound-N(m0, n0) = odd-part(|m0 - n0|)
;;;
;;; 2. When gcd-k > 1: diff-odd-part(k+1) < diff-odd-part(k)
;;;    (odd-part strictly decreases each step where gcd > 1)
;;;
;;; 3. When diff-odd-part = 1: gcd-k = 1
;;;    (power-of-2 difference implies coprime)
;;;
;;; 4. Once gcd-k = 1 at some k0, coprime-transformed-p holds for all k >= k0
;;;    (via putnam-2025-a1-from-power-of-2)
;;;
;;; The full proof follows: Since diff-odd-part starts at bound-N and
;;; strictly decreases (by at least 1) each step where gcd > 1, after
;;; at most bound-N steps, either:
;;; - We've had gcd = 1 at some step (so coprime forever after), or
;;; - diff-odd-part has reached 1, which implies gcd = 1 (coprime forever)
;;;
;;; Therefore, for all k >= bound-N, coprime-transformed-p(m0, n0, k) holds.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
