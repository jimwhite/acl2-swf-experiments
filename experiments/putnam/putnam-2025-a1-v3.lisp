(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - SOLUTION (v3 with arithmetic-5)
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

;; Use arithmetic-5 FIRST for better nonlinear arithmetic support
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
  (implies (posp n)
           (posp (odd-part n)))
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
  (implies (posp n)
           (oddp (odd-part n)))
  :hints (("Goal" :induct (odd-part n))))

(defthm odd-part-of-two-times
  (implies (posp n)
           (equal (odd-part (* 2 n)) (odd-part n)))
  :hints (("Goal" :expand (odd-part (* 2 n)))))

(defun power-of-2-p (n)
  (declare (xargs :guard (posp n)))
  (equal (odd-part n) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: GCD PROPERTIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-posp-type
  (implies (and (posp x) (posp y))
           (posp (dm::gcd x y)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x x) (y y)))))
  :rule-classes (:rewrite :type-prescription))

(defun gcd-odd-two-ind (g)
  (declare (xargs :measure (nfix g)))
  (if (or (zp g) (= g 1)) 1
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: ODD DIVISORS AND ODD-PART
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm divides-equiv
  (implies (and (posp n) (posp g))
           (iff (dm::divides g n)
                (integerp (/ n g))))
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
  (implies (and (integerp a) (integerp b) (evenp b))
           (evenp (* a b)))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm odd-div-by-odd-is-odd
  (implies (and (posp n) (posp g) (oddp n) (oddp g) (integerp (/ n g)))
           (oddp (/ n g)))
  :hints (("Goal" :in-theory (enable oddp evenp)
                  :use (:instance odd-times-even-is-even (a g) (b (/ n g))))))

(defthm odd-part-div-by-odd-when-n-odd
  (implies (and (posp n) (posp g) (oddp n) (oddp g) (integerp (/ n g)))
           (equal (odd-part (/ n g))
                  (/ (odd-part n) g)))
  :hints (("Goal" :use odd-div-by-odd-is-odd
                  :in-theory (disable odd-div-by-odd-is-odd))))

(defthm odd-part-div-by-odd
  (implies (and (posp n) (posp g) (oddp g) (dm::divides g n))
           (equal (odd-part (/ n g))
                  (/ (odd-part n) g)))
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
  (declare (xargs :guard (and (posp num) (posp den))
                  :verify-guards nil))
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
  (declare (xargs :guard (and (posp m) (posp n))
                  :verify-guards nil))
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

;; Key relationship: |m' - n'| = 2|m-n|/g
(defthm next-mn-diff
  (implies (and (natp m) (natp n))
           (equal (- (car (next-mn m n)) (cdr (next-mn m n)))
                  (/ (* 2 (- m n))
                     (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))))
  :hints (("Goal" :in-theory (enable reduce-to-lowest-terms next-mn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: GCD OF ODD NUMBERS IS ODD
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-integerp
  (implies (and (posp a) (posp b))
           (integerp (dm::gcd a b)))
  :hints (("Goal" :use (:instance dm::gcd-pos (x a) (y b)))))

(defthm even-times-is-even
  (implies (and (integerp a) (integerp b) (evenp a))
           (evenp (* a b)))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm divisor-of-odd-is-odd
  (implies (and (integerp a) (integerp d) 
                (not (equal d 0))
                (oddp a)
                (integerp (/ a d)))
           (oddp d))
  :hints (("Goal" :use (:instance even-times-is-even (a d) (b (/ a d)))
                  :in-theory (e/d (oddp) (even-times-is-even evenp)))))

(defthm gcd-of-odds-is-odd
  (implies (and (posp a) (oddp a) (posp b) (oddp b))
           (oddp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))
                        (:instance divisor-of-odd-is-odd 
                                   (a a) 
                                   (d (dm::gcd a b))))
                  :in-theory (enable dm::divides))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: GCD DIVIDES DIFFERENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm two-m-plus-one-oddp
  (implies (integerp m)
           (oddp (+ 1 (* 2 m))))
  :hints (("Goal" :in-theory (enable oddp evenp))))

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

(defthm gcd-posp
  (implies (and (posp a) (posp b))
           (posp (dm::gcd a b)))
  :hints (("Goal" :use (:instance dm::gcd-pos (x a) (y b)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 7: ODD DIVISOR OF POWER OF 2 IS 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm divides-one-implies-one
  (implies (and (posp d) (dm::divides d 1))
           (equal d 1))
  :hints (("Goal" :in-theory (enable dm::divides)))
  :rule-classes nil)

(defthm odd-divides-power-of-2-diff
  (implies (and (posp d) (posp n) (oddp d)
                (equal (odd-part n) 1)
                (dm::divides d n))
           (equal d 1))
  :hints (("Goal" :use ((:instance odd-divides-n-implies-divides-odd-part (g d))
                        (:instance divides-one-implies-one))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 8: MAIN THEOREM - POWER OF 2 DIFFERENCE IMPLIES GCD = 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Case 1: m > n
(defthm gcd-is-one-when-diff-is-power-of-2-case-1
  (implies (and (natp m) (natp n) (> m n)
                (power-of-2-p (- m n)))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use ((:instance odd-divides-power-of-2-diff
                                   (d (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (n (- m n)))
                        gcd-two-m-n-divides-diff
                        gcd-two-m-n-plus-one-oddp)
                  :in-theory (enable power-of-2-p))))

;; GCD is symmetric
(defthm gcd-symmetric
  (equal (dm::gcd a b) (dm::gcd b a))
  :hints (("Goal" :in-theory (enable dm::gcd))))

;; Case 2: m < n (use symmetry)
(defthm gcd-is-one-when-diff-is-power-of-2-case-2
  (implies (and (natp m) (natp n) (< m n)
                (power-of-2-p (- n m)))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :use ((:instance gcd-is-one-when-diff-is-power-of-2-case-1
                                   (m n) (n m))
                        gcd-symmetric)
                  :in-theory (disable gcd-is-one-when-diff-is-power-of-2-case-1))))

;; Combined theorem
(defthm gcd-is-one-when-diff-is-power-of-2
  (implies (and (natp m) (natp n) (not (= m n))
                (power-of-2-p (abs (- m n))))
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))) 1))
  :hints (("Goal" :cases ((> m n) (< m n))
                  :in-theory (enable abs))))
