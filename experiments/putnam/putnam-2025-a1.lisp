(in-package "ACL2")

;; Include necessary books
(include-book "projects/numbers/euclid" :dir :system)
(include-book "arithmetic/top" :dir :system)

;; GCD properties: establish that gcd of positive integers is positive
(defthm gcd-posp-type
  (implies (and (posp x) (posp y))
           (posp (dm::gcd x y)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x x) (y y)))))
  :rule-classes (:rewrite :type-prescription))

;; GCD divides its arguments (needed for division operations)
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

;; The transformation function: 2m+1
(defun next-num (m)
  (declare (xargs :guard (natp m)))
  (+ (* 2 m) 1))

(defthm next-num-posp
  (implies (natp m)
           (posp (next-num m)))
  :rule-classes (:rewrite :type-prescription))

;; Reduce a fraction to lowest terms
(defun reduce-fraction (num den)
  (declare (xargs :guard (and (posp num) (posp den))))
  (let ((g (dm::gcd num den)))
    (cons (/ num g) (/ den g))))

;; One iteration: (m, n) -> (m', n') where m'/n' = (2m+1)/(2n+1) in lowest terms
(defun next-pair (m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (reduce-fraction (next-num m) (next-num n)))

;; Test examples (run interactively, not in book):
;; (next-pair 3 5)   => (7 . 11)  ;; (2*3+1)/(2*5+1) = 7/11
;; (next-pair 1 4)   => (1 . 3)   ;; (2*1+1)/(2*4+1) = 3/9 = 1/3
;; (next-pair 1 3)   => (3 . 7)   ;; (2*1+1)/(2*3+1) = 3/7

(defthm two-m-plus-one-oddp
  (implies (integerp m)
           (oddp (+ 1 (* 2 m))))
  :hints (("Goal" :in-theory (enable oddp evenp))))

;; Need uncertified book for evenp-times lemma
(include-book "projects/numbers/eisenstein" :dir :system)

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
                        (:instance two-m-plus-one-oddp (m n))
                        (:instance next-num-posp (m m))
                        (:instance next-num-posp (m n)))
                  :in-theory (disable oddp two-m-plus-one-oddp next-num-posp))))

(defthm divides-diff
  (implies (and (dm::divides g a) (dm::divides g b))
           (dm::divides g (- a b)))
  :hints (("Goal" :use ((:instance dm::divides-minus (x g) (y b))
                        (:instance dm::divides-sum (x g) (y a) (z (- b)))))))

;; gcd(2m+1, 2n+1) divides 2(m-n) = (2m+1) - (2n+1)
(defthm gcd-divides-two-times-diff
  (implies (and (natp m) (natp n))
           (dm::divides (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))
                        (* 2 (- m n))))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x (+ 1 (* 2 m))) (y (+ 1 (* 2 n))))
                        (:instance divides-diff 
                                   (g (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n))))
                                   (a (+ 1 (* 2 m)))
                                   (b (+ 1 (* 2 n))))))))

;; Helper for induction
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

(defthm divides-one-implies-one
  (implies (and (posp d) (dm::divides d 1))
           (equal d 1))
  :hints (("Goal" :in-theory (enable dm::divides)))
  :rule-classes nil)

(defthm odd-divides-power-of-2-implies-1
  (implies (and (natp k) (posp d) (oddp d) (dm::divides d (expt 2 k)))
           (equal d 1))
  :hints (("Goal" :induct (expt 2 k))
          ("Subgoal *1/3" :use ((:instance odd-divides-two-times-implies-divides
                                           (g d) (k (expt 2 (1- k))))))
          ("Subgoal *1/1" :use divides-one-implies-one))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: THE MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; odd-part: the largest odd divisor of n
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

;; log2 for expressing two-part as 2^k
(defun log2 (n)
  (declare (xargs :guard (posp n)
                  :measure (nfix n)))
  (if (or (zp n) (= n 1))
      0
    (if (evenp n)
        (+ 1 (log2 (/ n 2)))
      0)))

;; Key properties
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

;; If odd d divides 2^k * m, then d divides m
(defthm odd-divides-product-with-power-of-2
  (implies (and (natp k) (posp d) (oddp d) (integerp m) (> m 0)
                (dm::divides d (* (expt 2 k) m)))
           (dm::divides d m))
  :hints (("Goal" :induct (expt 2 k))
          ("Subgoal *1/2" :use ((:instance odd-divides-two-times-implies-divides
                                           (g d) (k (* (expt 2 (- k 1)) m)))))))

;; Key lemma: odd d divides n implies d divides odd-part(n)
(defthm odd-divides-implies-divides-odd-part
  (implies (and (posp n) (posp d) (oddp d) (dm::divides d n))
           (dm::divides d (odd-part n)))
  :hints (("Goal" :use ((:instance n-equals-odd-times-two-part)
                        (:instance odd-divides-product-with-power-of-2
                                   (k (log2 n)) (m (odd-part n)))))))

;; A number is a power of 2 iff its odd-part is 1
(defun power-of-2-p (n)
  (declare (xargs :guard (posp n)))
  (equal (odd-part n) 1))

;; g | n and g | odd-part(n), and odd-part(n) = 1, then g = 1
(defthm odd-divides-power-of-2-diff
  (implies (and (posp d) (posp n) (oddp d)
                (equal (odd-part n) 1)
                (dm::divides d n))
           (equal d 1))
  :hints (("Goal" :use ((:instance odd-divides-implies-divides-odd-part)
                        (:instance divides-one-implies-one))))
  :rule-classes nil)

;; g divides (m - n) also means g divides (n - m) = -(m - n)
(defthm divides-neg
  (implies (dm::divides g x)
           (dm::divides g (- x)))
  :hints (("Goal" :in-theory (enable dm::divides))))

;; gcd divides absolute difference
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

;;; MAIN THEOREM ;;;
;; If |m-n| is a power of 2, then gcd(2m+1, 2n+1) = 1
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

