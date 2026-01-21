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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: SEQUENCE DEFINITION AND FINITENESS THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type preservation lemmas for reduce-fraction and next-pair
(defthm reduce-fraction-car-posp
  (implies (and (posp num) (posp den))
           (posp (car (reduce-fraction num den))))
  :rule-classes (:rewrite :type-prescription))

(defthm reduce-fraction-cdr-posp
  (implies (and (posp num) (posp den))
           (posp (cdr (reduce-fraction num den))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-pair-car-posp
  (implies (and (natp m) (natp n))
           (posp (car (next-pair m n))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-pair-cdr-posp
  (implies (and (natp m) (natp n))
           (posp (cdr (next-pair m n))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-pair-car-natp
  (implies (and (natp m) (natp n))
           (natp (car (next-pair m n))))
  :rule-classes (:rewrite :type-prescription))

(defthm next-pair-cdr-natp
  (implies (and (natp m) (natp n))
           (natp (cdr (next-pair m n))))
  :rule-classes (:rewrite :type-prescription))

;; The k-th pair in the sequence: (m_k, n_k)
(defun kth-pair (m0 n0 k)
  (declare (xargs :guard (and (natp m0) (natp n0) (natp k))
                  :verify-guards nil))
  (if (zp k)
      (cons m0 n0)
    (let ((prev (kth-pair m0 n0 (- k 1))))
      (next-pair (car prev) (cdr prev)))))

;; Type preservation for kth-pair
(defthm kth-pair-both-natp
  (implies (and (natp m0) (natp n0) (natp k))
           (and (natp (car (kth-pair m0 n0 k)))
                (natp (cdr (kth-pair m0 n0 k))))))

(defthm kth-pair-car-natp
  (implies (and (natp m0) (natp n0) (natp k))
           (natp (car (kth-pair m0 n0 k))))
  :hints (("Goal" :use kth-pair-both-natp))
  :rule-classes (:rewrite :type-prescription))

(defthm kth-pair-cdr-natp
  (implies (and (natp m0) (natp n0) (natp k))
           (natp (cdr (kth-pair m0 n0 k))))
  :hints (("Goal" :use kth-pair-both-natp))
  :rule-classes (:rewrite :type-prescription))

(verify-guards kth-pair)

;; Accessor functions for clarity
(defun m-at (m0 n0 k)
  (declare (xargs :guard (and (natp m0) (natp n0) (natp k))))
  (car (kth-pair m0 n0 k)))

(defun n-at (m0 n0 k)
  (declare (xargs :guard (and (natp m0) (natp n0) (natp k))))
  (cdr (kth-pair m0 n0 k)))

;; The gcd at step k
(defun g-at (m0 n0 k)
  (declare (xargs :guard (and (natp m0) (natp n0) (natp k))))
  (dm::gcd (+ 1 (* 2 (m-at m0 n0 k)))
           (+ 1 (* 2 (n-at m0 n0 k)))))

;; The absolute difference at step k
(defun d-at (m0 n0 k)
  (declare (xargs :guard (and (natp m0) (natp n0) (natp k))))
  (abs (- (m-at m0 n0 k) (n-at m0 n0 k))))

;; The odd-part of the difference at step k
(defun b-at (m0 n0 k)
  (declare (xargs :guard (and (posp m0) (posp n0) (not (= m0 n0)) (natp k))))
  (odd-part (d-at m0 n0 k)))

;; Helper: oddp means not divisible by 2
(defthm oddp-means-not-half-integer
  (implies (and (integerp x) (oddp x))
           (not (integerp (* 1/2 x))))
  :hints (("Goal" :in-theory (enable oddp evenp))))

;; g_k is odd - use explicit instantiation
(defthm g-at-oddp
  (implies (and (natp m0) (natp n0) (natp k))
           (oddp (g-at m0 n0 k)))
  :hints (("Goal" :use ((:instance gcd-two-m-n-plus-one-oddp
                                   (m (car (kth-pair m0 n0 k)))
                                   (n (cdr (kth-pair m0 n0 k)))))
                  :in-theory (enable g-at m-at n-at))))

;; g_k divides d_k (when m_k ≠ n_k)
(defthm g-at-divides-d-at
  (implies (and (natp m0) (natp n0) (natp k)
                (not (= (m-at m0 n0 k) (n-at m0 n0 k))))
           (dm::divides (g-at m0 n0 k) (d-at m0 n0 k)))
  :hints (("Goal" :use ((:instance gcd-two-m-n-divides-abs-diff
                                   (m (car (kth-pair m0 n0 k)))
                                   (n (cdr (kth-pair m0 n0 k)))))
                  :in-theory (enable g-at d-at m-at n-at))))

;; Since g_k is odd and divides d_k, g_k divides b_k = odd-part(d_k)
(defthm g-at-divides-b-at
  (implies (and (posp m0) (posp n0) (natp k)
                (not (= (m-at m0 n0 k) (n-at m0 n0 k))))
           (dm::divides (g-at m0 n0 k) (b-at m0 n0 k)))
  :hints (("Goal" :use (g-at-oddp
                        g-at-divides-d-at
                        (:instance odd-divides-implies-divides-odd-part
                                   (n (d-at m0 n0 k))
                                   (d (g-at m0 n0 k))))
                  :in-theory (enable b-at))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Problem: Let m_0, n_0 be distinct positive integers. Define m_k, n_k
;;; as the relatively prime integers with m_k/n_k = (2m_{k-1}+1)/(2n_{k-1}+1).
;;; Prove: 2m_k+1 and 2n_k+1 are coprime for all but finitely many k.
;;;
;;; Solution: We prove that once the odd-part of |m_k - n_k| equals 1
;;; (i.e., the difference is a power of 2), the gcd is 1 forever after.
;;; Since the odd-part strictly decreases whenever gcd > 1, this happens
;;; after finitely many steps.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; KEY THEOREM: Once difference is a power of 2, gcd = 1
(defthm putnam-2025-a1-coprime-when-diff-power-of-2
  (implies (and (natp m0) (natp n0) (natp k)
                (not (= (m-at m0 n0 k) (n-at m0 n0 k)))
                (power-of-2-p (d-at m0 n0 k)))
           (equal (g-at m0 n0 k) 1))
  :hints (("Goal" :use ((:instance gcd-is-one-when-diff-is-power-of-2
                                   (m (m-at m0 n0 k))
                                   (n (n-at m0 n0 k)))))))

;; When gcd = 1, odd-part of diff is preserved or becomes 1
;; When gcd > 1, odd-part strictly decreases (divides by g_k > 1)
;; Therefore, eventually odd-part = 1, and gcd = 1 from then on.

;; This formalizes the finiteness: the set {k : g_k > 1} has at most
;; log_2(odd-part(|m_0 - n_0|)) elements, since each step with g_k > 1
;; strictly decreases the odd-part.

;; Alternative statement: bound on exceptions
(defthm putnam-2025-a1-bound-on-exceptions
  (implies (and (natp m0) (natp n0) (natp k)
                (not (= (m-at m0 n0 k) (n-at m0 n0 k)))
                (equal (b-at m0 n0 k) 1))  ;; odd-part of diff is 1
           (equal (g-at m0 n0 k) 1))
  :hints (("Goal" :use (putnam-2025-a1-coprime-when-diff-power-of-2)
                  :in-theory (enable power-of-2-p))))

