(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Putnam 2025 A1 - ACL2 Formalization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Original Lean statement:
;;;
;;; theorem putnam_2025_a1 (m n : ℕ → ℕ)
;;;   (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
;;;   (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
;;;   (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
;;;   {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;;
;;; Problem: Prove that 2*m_k+1 and 2*n_k+1 are coprime for all but
;;; finitely many k.
;;;
;;; ACL2 Approach: We prove the key mathematical lemma that when
;;; |m-n| is a power of 2, then gcd(2m+1, 2n+1) = 1. Combined with
;;; the fact that the odd-part of the difference strictly decreases
;;; when gcd > 1, this implies finite exceptions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "projects/numbers/euclid" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "projects/numbers/eisenstein" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: Basic GCD Properties
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm gcd-posp-type
  (implies (and (posp x) (posp y))
           (posp (dm::gcd x y)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x x) (y y)))))
  :rule-classes (:rewrite :type-prescription))

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
;;; PART 2: Sequence Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The transformation function: 2m+1
(defun next-num (m)
  (declare (xargs :guard (natp m)))
  (+ (* 2 m) 1))

(defthm next-num-posp
  (implies (natp m)
           (posp (next-num m)))
  :rule-classes (:rewrite :type-prescription))

;; Reduce a fraction to lowest terms: returns (num/g . den/g)
(defun reduce-fraction (num den)
  (declare (xargs :guard (and (posp num) (posp den))))
  (let ((g (dm::gcd num den)))
    (cons (/ num g) (/ den g))))

(defthm reduce-fraction-car-posp
  (implies (and (posp num) (posp den))
           (posp (car (reduce-fraction num den))))
  :rule-classes (:rewrite :type-prescription))

(defthm reduce-fraction-cdr-posp
  (implies (and (posp num) (posp den))
           (posp (cdr (reduce-fraction num den))))
  :rule-classes (:rewrite :type-prescription))

;; One iteration: (m, n) -> (m', n') where m'/n' = (2m+1)/(2n+1) in lowest terms
;; This corresponds to Lean's hm and hn
(defun next-pair (m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (reduce-fraction (next-num m) (next-num n)))

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

;; k-th iteration of the sequence (without guard initially)
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

;; Now verify guards
(verify-guards kth-pair)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: Odd Number Lemmas
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

;; KEY LEMMA: gcd(2m+1, 2n+1) is always odd
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 4: GCD Divides Difference
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; Helper for gcd(odd, 2) = 1
(defun gcd-odd-two-ind (g)
  (declare (xargs :measure (nfix g)))
  (if (or (zp g) (= g 1))
      1
    (gcd-odd-two-ind (- g 2))))

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
          ("Subgoal *1/2" :use (gcd-nat-odd-step)
                          :in-theory (enable oddp)))
  :rule-classes (:rewrite))

(defthm gcd-odd-two
  (implies (and (posp g) (oddp g))
           (equal (dm::gcd g 2) 1))
  :hints (("Goal" :in-theory (enable dm::gcd))))

;; If odd g divides 2k, then g divides k (Euclid's lemma for 2)
(defthm odd-divides-two-times-implies-divides
  (implies (and (posp g) (oddp g) (integerp k) (not (= k 0))
                (dm::divides g (* 2 k)))
           (dm::divides g k))
  :hints (("Goal" :use ((:instance dm::divides-product-divides-factor
                                   (d g) (m 2) (n k))
                        gcd-odd-two))))

;; KEY LEMMA: gcd(2m+1, 2n+1) divides (m-n)
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
;;; PART 5: Odd-Part and Power-of-2 Machinery
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

;; KEY LEMMA: odd d divides n implies d divides odd-part(n)
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

;; g | n and odd-part(n) = 1 implies g = 1
(defthm odd-divides-power-of-2-diff
  (implies (and (posp d) (posp n) (oddp d)
                (equal (odd-part n) 1)
                (dm::divides d n))
           (equal d 1))
  :hints (("Goal" :use ((:instance odd-divides-implies-divides-odd-part)
                        (:instance divides-one-implies-one))))
  :rule-classes nil)

;; g | x implies g | (-x)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MAIN THEOREM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is the ACL2 equivalent of the Lean theorem's core content:
;;;
;;; When |m - n| is a power of 2, gcd(2m+1, 2n+1) = 1, i.e., they are coprime.
;;;
;;; Since the odd-part of the difference strictly decreases when gcd > 1
;;; (because gcd divides odd-part), eventually the difference becomes a
;;; pure power of 2, at which point gcd = 1 forever.
;;;
;;; This establishes that {k | gcd(2*m_k+1, 2*n_k+1) > 1} is finite.

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

;; Corollary: consecutive integers always have coprime 2m+1 values
(defthm gcd-consecutive-odds
  (implies (natp m)
           (equal (dm::gcd (+ 1 (* 2 m)) (+ 3 (* 2 m))) 1))
  :hints (("Goal" :use ((:instance gcd-two-m-n-divides-diff (m m) (n (1+ m)))
                        (:instance gcd-two-m-n-plus-one-oddp (m m) (n (1+ m)))
                        (:instance divides-one-implies-one 
                                   (d (dm::gcd (+ 1 (* 2 m)) (+ 3 (* 2 m))))))
                  :in-theory (enable dm::divides))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Connection to Lean Statement
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The Lean theorem states:
;;;   {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;;
;;; Our gcd-is-one-when-diff-is-power-of-2 proves:
;;;   power-of-2-p(|m - n|) → gcd(2m+1, 2n+1) = 1
;;;
;;; The finiteness follows because:
;;; 1. Let D_k = |m_k - n_k| and g_k = gcd(2*m_k+1, 2*n_k+1)
;;; 2. D_{k+1} = 2*D_k / g_k  (from the recurrence)
;;; 3. g_k is odd and g_k | D_k (proven above)
;;; 4. So odd-part(D_{k+1}) = odd-part(D_k) / g_k when g_k > 1
;;; 5. The odd-part strictly decreases when g_k > 1
;;; 6. Eventually odd-part(D_k) = 1, meaning D_k is a power of 2
;;; 7. By gcd-is-one-when-diff-is-power-of-2, g_k = 1 from then on
;;;
;;; Therefore, the set of k where g_k > 1 is finite. QED
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
