;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; putnam-2025-a1-lean-translation.lisp
;;;
;;; Direct translation of Lean4 Putnam 2025 A1 proof to ACL2.
;;; 
;;; Source:
;;;   https://github.com/project-numina/Numina-Putnam2025/blob/main/NuminaPutnam2025/putnam_2025_a1.lean
;;;
;;; The Lean4 theorem statement is:
;;;   {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;;
;;; ACL2 formulation:
;;;   For any K, count-bad(m0, n0, K) < D(0) = |m0 - n0|
;;;   i.e., the set of "bad" indices has strictly fewer than |m0 - n0| elements.
;;;
;;; Translation from Lean4 by Jim White and GitHub Copilot (Opus 4.5) with assistance by Perplexity.
;;; Date: January 2026
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; For dm::gcd and dm::divides
(include-book "projects/numbers/euclid" :dir :system)

;; For arithmetic
(include-book "arithmetic-5/top" :dir :system)

;; For evenp-times (product of odd numbers is odd)
(include-book "projects/numbers/eisenstein" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; BRIDGE LEMMAS: Connecting dm::divides to integerp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; These derive from the definition of dm::divides and dm::gcd-divides

;; dm::divides means the quotient is an integer (from definition)
(defthm divides-means-integerp-quotient
  (implies (dm::divides d a)
           (integerp (/ a d)))
  :hints (("Goal" :in-theory (enable dm::divides))))

;; gcd(a,b) divides a when a is nonzero (instance of dm::gcd-divides)
(defthm gcd-divides-first
  (implies (and (integerp a) (integerp b) (not (equal a 0)))
           (dm::divides (dm::gcd a b) a))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))))))

;; Combining: a/gcd(a,b) is an integer
(defthm quotient-by-gcd-integerp
  (implies (and (integerp a) (integerp b) (not (equal a 0)))
           (integerp (/ a (dm::gcd a b))))
  :hints (("Goal" :use ((:instance gcd-divides-first)
                        (:instance divides-means-integerp-quotient 
                                   (d (dm::gcd a b)))))))

;; gcd is positive when inputs are positive (instance of dm::gcd-pos)
(defthm gcd-posp
  (implies (and (posp a) (posp b))
           (posp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance dm::gcd-pos (x a) (y b)))))
  :rule-classes :type-prescription)

;; a/gcd(a,b) is positive when a is positive
(defthm quotient-by-gcd-posp
  (implies (and (posp a) (posp b))
           (posp (/ a (dm::gcd a b))))
  :hints (("Goal" :use ((:instance quotient-by-gcd-integerp)
                        (:instance gcd-posp))))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 1: ODD-PART FUNCTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lean4: let oddPart : ℕ → ℕ := fun n => n / 2 ^ n.factorization 2

(defun odd-part (n)
  "Remove all factors of 2 from n. Returns n if n is odd, n/2^k where k is maximal."
  (declare (xargs :guard (natp n)
                  :measure (nfix n)))
  (if (or (zp n) (not (integerp (/ n 2))))
      n
    (odd-part (/ n 2))))

;; Basic properties
(defthm odd-part-posp
  (implies (posp n)
           (posp (odd-part n)))
  :rule-classes (:rewrite :type-prescription))

(defthm odd-part-leq
  (implies (posp n)
           (<= (odd-part n) n))
  :rule-classes :linear)

(defthm odd-part-of-1
  (equal (odd-part 1) 1))

(defthm odd-part-odd
  (implies (and (posp n) (not (integerp (/ n 2))))
           (equal (odd-part n) n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 2: SEQUENCE DEFINITION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lean4:
;;;   (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
;;;   (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den)
;;;
;;; The rational p/q reduced to lowest terms has:
;;;   numerator = p / gcd(p,q)
;;;   denominator = q / gcd(p,q)

;; Coerce to positive integer, defaulting to 1
(defun pos-fix (x)
  (if (posp x) x 1))

(defun next-mn (m n)
  "Given (m, n), return (m', n') where m'/n' = (2m+1)/(2n+1) reduced to lowest terms.
   Coerces non-positive inputs to 1."
  (let* ((m (pos-fix m))
         (n (pos-fix n))
         (a (+ 1 (* 2 m)))
         (b (+ 1 (* 2 n)))
         (g (dm::gcd a b)))
    (cons (/ a g) (/ b g))))

(defun mn-seq (m0 n0 k)
  "Return (m_k . n_k) for the sequence starting at (m0, n0).
   Coerces non-positive m0/n0 to 1, non-natural k to 0."
  (declare (xargs :measure (nfix k)))
  (let ((m0 (pos-fix m0))
        (n0 (pos-fix n0)))
    (if (zp k)
        (cons m0 n0)
      (let ((prev (mn-seq m0 n0 (1- k))))
        (next-mn (car prev) (cdr prev))))))

(defun m-k (m0 n0 k) (car (mn-seq m0 n0 k)))
(defun n-k (m0 n0 k) (cdr (mn-seq m0 n0 k)))

;; 2m+1 is positive when m is positive
(defthm two-m-plus-one-posp
  (implies (posp m)
           (posp (+ 1 (* 2 m))))
  :rule-classes :type-prescription)

;; next-mn returns positive car
(defthm next-mn-car-posp
  (posp (car (next-mn m n)))
  :hints (("Goal" :in-theory (enable next-mn)
                  :use ((:instance quotient-by-gcd-posp
                                   (a (+ 1 (* 2 (pos-fix m))))
                                   (b (+ 1 (* 2 (pos-fix n))))))))
  :rule-classes :type-prescription)

;; next-mn returns positive cdr
(defthm next-mn-cdr-posp
  (posp (cdr (next-mn m n)))
  :hints (("Goal" :in-theory (enable next-mn)
                  :use ((:instance quotient-by-gcd-posp
                                   (a (+ 1 (* 2 (pos-fix n))))
                                   (b (+ 1 (* 2 (pos-fix m)))))
                        (:instance dm::gcd-commutative
                                   (x (+ 1 (* 2 (pos-fix m))))
                                   (y (+ 1 (* 2 (pos-fix n))))))))
  :rule-classes :type-prescription)

;; mn-seq returns a pair of positive integers (proved by simultaneous induction)
(defthm mn-seq-posp-pair
  (and (posp (car (mn-seq m0 n0 k)))
       (posp (cdr (mn-seq m0 n0 k))))
  :hints (("Goal" :induct (mn-seq m0 n0 k)
                  :in-theory (enable mn-seq next-mn))
          ("Subgoal *1/2" 
           :use ((:instance quotient-by-gcd-posp
                            (a (+ 1 (* 2 (car (mn-seq (pos-fix m0) (pos-fix n0) (1- k))))))
                            (b (+ 1 (* 2 (cdr (mn-seq (pos-fix m0) (pos-fix n0) (1- k)))))))
                 (:instance quotient-by-gcd-posp
                            (a (+ 1 (* 2 (cdr (mn-seq (pos-fix m0) (pos-fix n0) (1- k))))))
                            (b (+ 1 (* 2 (car (mn-seq (pos-fix m0) (pos-fix n0) (1- k)))))))
                 (:instance dm::gcd-commutative
                            (x (+ 1 (* 2 (car (mn-seq (pos-fix m0) (pos-fix n0) (1- k))))))
                            (y (+ 1 (* 2 (cdr (mn-seq (pos-fix m0) (pos-fix n0) (1- k))))))))))
  :rule-classes ((:type-prescription :corollary (posp (car (mn-seq m0 n0 k))))
                 (:type-prescription :corollary (posp (cdr (mn-seq m0 n0 k))))))

;; Accessor type rules (derived from mn-seq-posp-pair)
(defthm m-k-posp
  (posp (m-k m0 n0 k))
  :rule-classes :type-prescription)

(defthm n-k-posp
  (posp (n-k m0 n0 k))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 3: GCD AND DIFFERENCE FUNCTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lean4:
;;;   let D : ℕ → ℕ := fun k => if m k ≥ n k then m k - n k else n k - m k
;;;   let g : ℕ → ℕ := fun k => (2 * m k + 1).gcd (2 * n k + 1)

(defun g-k (m0 n0 k)
  "g(k) = gcd(2*m_k + 1, 2*n_k + 1)"
  (let ((m (m-k m0 n0 k))
        (n (n-k m0 n0 k)))
    (dm::gcd (+ 1 (* 2 m)) (+ 1 (* 2 n)))))

(defun D-k (m0 n0 k)
  "D(k) = |m_k - n_k|"
  (abs (- (m-k m0 n0 k) (n-k m0 n0 k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 4: PRODUCT OF GCDs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lean4: (Finset.range K).prod g
;;; This is the product g(0) * g(1) * ... * g(K-1)

(defun prod-g (m0 n0 k)
  "Product of g(0), g(1), ..., g(k-1). Empty product (k=0) is 1."
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (* (g-k m0 n0 (1- k)) (prod-g m0 n0 (1- k)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 5: KEY LEMMAS FROM LEAN4 (PROVEN)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper lemmas for recurrence proofs

;; g-k in terms of mn-seq
(defthm g-k-expand
  (equal (g-k m0 n0 k)
         (dm::gcd (+ 1 (* 2 (car (mn-seq m0 n0 k))))
                  (+ 1 (* 2 (cdr (mn-seq m0 n0 k))))))
  :hints (("Goal" :in-theory (enable g-k m-k n-k))))

;; mn-seq at k+1 in terms of next-mn at k
(defthm mn-seq-step
  (implies (natp k)
           (equal (mn-seq m0 n0 (+ 1 k))
                  (next-mn (car (mn-seq m0 n0 k))
                           (cdr (mn-seq m0 n0 k)))))
  :hints (("Goal" :in-theory (enable mn-seq)
                  :expand ((mn-seq m0 n0 (+ 1 k))))))

;;; LEMMA 4 (Lean4: hD_rec): D(k+1) * g(k) = 2 * D(k)
;;; KEY RECURRENCE - PROVEN!
(defthm D-recurrence
  (implies (natp k)
           (equal (* (D-k m0 n0 (+ 1 k)) (g-k m0 n0 k))
                  (* 2 (D-k m0 n0 k))))
  :hints (("Goal" :in-theory (enable D-k m-k n-k g-k mn-seq next-mn))))

;; Algebra helper for product formula
(defthm algebra-helper
  (implies (and (equal (* d-succ g) (* 2 d-prev))
                (equal (* d-prev pg) (* exp d0))
                (acl2-numberp d-succ)
                (acl2-numberp d-prev)
                (acl2-numberp d0)
                (acl2-numberp g)
                (acl2-numberp pg)
                (acl2-numberp exp))
           (equal (* d-succ g pg) (* 2 exp d0))))

;;; LEMMA 5 (Lean4: hprod_formula): D(K) * prod-g(K) = 2^K * D(0)
;;; PROVEN!
(defthm product-formula
  (implies (natp k)
           (equal (* (D-k m0 n0 k) (prod-g m0 n0 k))
                  (* (expt 2 k) (D-k m0 n0 0))))
  :hints (("Goal" :induct (prod-g m0 n0 k)
                  :in-theory (e/d (prod-g)
                                  (D-k g-k mn-seq m-k n-k next-mn pos-fix D-recurrence)))
          ("Subgoal *1/2" 
           :use ((:instance D-recurrence (k (1- k)))
                 (:instance algebra-helper
                            (d-succ (D-k m0 n0 k))
                            (g (g-k m0 n0 (1- k)))
                            (d-prev (D-k m0 n0 (1- k)))
                            (pg (prod-g m0 n0 (1- k)))
                            (exp (expt 2 (1- k)))
                            (d0 (D-k m0 n0 0))))
           :in-theory (e/d (prod-g g-k-expand)
                           (D-k g-k mn-seq m-k n-k next-mn pos-fix D-recurrence algebra-helper)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ODDNESS LEMMAS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Definition of odd
(defun my-oddp (n)
  (and (integerp n)
       (not (integerp (/ n 2)))))

;; 2k+1 is odd
(defthm two-k-plus-one-odd
  (implies (integerp k)
           (my-oddp (+ 1 (* 2 k))))
  :hints (("Goal" :in-theory (enable my-oddp))))

;; If d is even and q is integer, then d*q is even
(defthm even-times-integer-is-even
  (implies (and (integerp (/ d 2))
                (integerp q))
           (integerp (/ (* d q) 2)))
  :hints (("Goal" :use ((:instance (:theorem (implies (integerp x) (integerp (* 2 x))))
                                   (x (* (/ d 2) q)))))))

;; A divisor of an odd number is odd
(defthm divisor-of-odd-is-odd
  (implies (and (my-oddp n)
                (dm::divides d n)
                (posp d))
           (my-oddp d))
  :hints (("Goal" :in-theory (enable my-oddp dm::divides)
                  :use ((:instance even-times-integer-is-even
                                   (q (/ n d)))))))

;; gcd of two odd positive numbers is odd
(defthm gcd-of-odds-is-odd
  (implies (and (my-oddp a) (my-oddp b) (posp a) (posp b))
           (my-oddp (dm::gcd a b)))
  :hints (("Goal" :use ((:instance divisor-of-odd-is-odd
                                   (n a)
                                   (d (dm::gcd a b)))
                        (:instance dm::gcd-divides (x a) (y b))
                        (:instance dm::gcd-pos (x a) (y b))))))

;;; LEMMA 2 (Lean4: hg_odd): g(k) is odd for all k - PROVEN!
(defthm g-k-is-odd
  (my-oddp (g-k m0 n0 k))
  :hints (("Goal" :in-theory (enable g-k m-k n-k)
                  :use ((:instance gcd-of-odds-is-odd
                                   (a (+ 1 (* 2 (car (mn-seq m0 n0 k)))))
                                   (b (+ 1 (* 2 (cdr (mn-seq m0 n0 k))))))))))

;; If n is odd and > 1, then n >= 3
(defthm odd-gt-1-means-geq-3
  (implies (and (my-oddp n) (> n 1))
           (>= n 3))
  :hints (("Goal" :in-theory (enable my-oddp))))

;; If g(k) > 1, then g(k) >= 3 (key for pigeonhole bound)
(defthm bad-g-geq-3
  (implies (> (g-k m0 n0 k) 1)
           (>= (g-k m0 n0 k) 3))
  :hints (("Goal" :use ((:instance g-k-is-odd)
                        (:instance odd-gt-1-means-geq-3 (n (g-k m0 n0 k)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DIVISIBILITY LEMMAS (using dm::divides-minus from euclid)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; gcd divides difference (combines dm::divides-sum with dm::divides-minus)
(defthm gcd-divides-diff
  (implies (and (integerp a) (integerp b) (not (equal a 0)) (not (equal b 0)))
           (dm::divides (dm::gcd a b) (- a b)))
  :hints (("Goal" :use ((:instance dm::gcd-divides (x a) (y b))
                        (:instance dm::divides-minus 
                                   (x (dm::gcd a b))
                                   (y b))
                        (:instance dm::divides-sum
                                   (x (dm::gcd a b))
                                   (y a)
                                   (z (- b)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ODD-PART LEMMAS (needed for hoddPart_descent)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Key fact: odd-part(n) = n when n is odd
(defthm odd-part-of-odd
  (implies (my-oddp n)
           (equal (odd-part n) n))
  :hints (("Goal" :in-theory (enable odd-part my-oddp))))

;; odd-part(2*n) = odd-part(n)
(defthm odd-part-of-double
  (implies (posp n)
           (equal (odd-part (* 2 n)) (odd-part n)))
  :hints (("Goal" :in-theory (enable odd-part)
                  :expand ((odd-part (* 2 n))))))

;; KEY LEMMA: odd-part(n/g) * g = odd-part(n) when g is odd and g|n
;; (This is hoddPart-descent-lemma-2 from the search results)
;; Proof idea: g is odd so doesn't affect factors of 2, only odd part

;; Helper: if g|n, then n/g is an integer
(defthm divides-implies-quotient-integerp
  (implies (and (posp g) (posp n)
                (dm::divides g n))
           (integerp (/ n g)))
  :hints (("Goal" :in-theory (enable dm::divides))))

;; Helper: if g|n, then n/g is positive
(defthm divides-implies-quotient-posp
  (implies (and (posp g) (posp n)
                (dm::divides g n))
           (posp (/ n g)))
  :hints (("Goal" :in-theory (enable dm::divides))))

;; Use dm::evenp-times: (evenp (* x y)) = (or (evenp x) (evenp y))
(defthm odd-times-odd-is-odd
  (implies (and (integerp m) (integerp n)
                (my-oddp m) (my-oddp n))
           (my-oddp (* m n)))
  :hints (("Goal" :in-theory (enable my-oddp)
                  :use (:instance dm::evenp-times (dm::x m) (dm::y n)))))

;; If m is odd, then odd-part(m * n) = m * odd-part(n)
;; When we multiply by an odd number, we don't add factors of 2
(defthm odd-part-times-odd
  (implies (and (posp m) (posp n) (my-oddp m))
           (equal (odd-part (* m n))
                  (* m (odd-part n))))
  :hints (("Goal" :in-theory (enable odd-part my-oddp))))

;; Main lemma: odd-part(n/g) * g = odd-part(n) when g is odd and g|n
(defthm odd-part-quotient-by-odd
  (implies (and (posp n) (posp g)
                (my-oddp g)
                (dm::divides g n))
           (equal (* g (odd-part (/ n g)))
                  (odd-part n)))
  :hints (("Goal" 
           :use ((:instance odd-part-times-odd 
                            (m g) 
                            (n (/ n g)))
                 (:instance divides-implies-quotient-posp
                            (g g) (n n)))
           :in-theory (disable odd-part-times-odd divides-implies-quotient-posp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DIVISIBILITY LEMMAS - g(k) DIVIDES D(k) (PROVEN!)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2 does not divide an odd number
(defthm two-not-divides-odd
  (implies (my-oddp g)
           (not (dm::divides 2 g)))
  :hints (("Goal" :in-theory (enable my-oddp dm::divides))))

;; If g is odd and g | 2x, then g | x (key: odd*integer=even iff integer is even)
(defthm odd-divides-double-implies-divides
  (implies (and (posp g)
                (integerp x)
                (my-oddp g)
                (dm::divides g (* 2 x)))
           (dm::divides g x))
  :hints (("Goal" :in-theory (enable dm::divides my-oddp)
                  :use ((:instance dm::evenp-times
                                   (dm::x g)
                                   (dm::y (/ (* 2 x) g)))))))

;; g(k) divides 2*(m(k) - n(k)) - follows from gcd-divides-diff
(defthm g-divides-twice-diff
  (implies (natp k)
           (dm::divides (g-k m0 n0 k)
                        (* 2 (- (m-k m0 n0 k) (n-k m0 n0 k)))))
  :hints (("Goal" :in-theory (enable g-k m-k n-k)
                  :use ((:instance gcd-divides-diff
                                   (a (+ 1 (* 2 (car (mn-seq m0 n0 k)))))
                                   (b (+ 1 (* 2 (cdr (mn-seq m0 n0 k))))))))))

;; g(k) divides (m(k) - n(k)) since g(k) is odd
(defthm g-divides-diff-raw
  (implies (natp k)
           (dm::divides (g-k m0 n0 k)
                        (- (m-k m0 n0 k) (n-k m0 n0 k))))
  :hints (("Goal" :use ((:instance g-divides-twice-diff)
                        (:instance odd-divides-double-implies-divides
                                   (g (g-k m0 n0 k))
                                   (x (- (m-k m0 n0 k) (n-k m0 n0 k))))
                        (:instance g-k-is-odd)))))

;; If d | x then d | |x|
(defthm divides-abs
  (implies (dm::divides d x)
           (dm::divides d (abs x)))
  :hints (("Goal" :in-theory (enable dm::divides)
                  :cases ((>= x 0)))))

;;; LEMMA 3 (Lean4: hg_dvd_D): g(k) | D(k) - PROVEN!
(defthm g-divides-D
  (implies (natp k)
           (dm::divides (g-k m0 n0 k) (D-k m0 n0 k)))
  :hints (("Goal" :in-theory (enable D-k)
                  :use ((:instance g-divides-diff-raw)
                        (:instance divides-abs
                                   (d (g-k m0 n0 k))
                                   (x (- (m-k m0 n0 k) (n-k m0 n0 k))))))))

;; If g is odd and g | n, then g | odd-part(n)
(defthm odd-divides-odd-part
  (implies (and (posp n) (posp g)
                (my-oddp g)
                (dm::divides g n))
           (dm::divides g (odd-part n)))
  :hints (("Goal" :in-theory (enable dm::divides)
                  :use ((:instance odd-part-quotient-by-odd (n n) (g g))
                        (:instance divides-implies-quotient-posp)))))

;; g(k) | odd-part(D(k))
(defthm g-divides-odd-part-D
  (implies (and (natp k) (posp (D-k m0 n0 k)))
           (dm::divides (g-k m0 n0 k) (odd-part (D-k m0 n0 k))))
  :hints (("Goal" :use ((:instance odd-divides-odd-part
                                   (g (g-k m0 n0 k))
                                   (n (D-k m0 n0 k)))
                        (:instance g-divides-D)
                        (:instance g-k-is-odd)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; REMAINING LEMMAS (TO BE PROVEN)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; LEMMA 1 (Lean4: hne): m_k ≠ n_k for all k
;;; (defthm mn-seq-distinct ...)

;;; LEMMA 6 (Lean4: hoddPart_descent): 
;;;   odd-part(D(K)) * prod-g(K) = odd-part(D(0))
;;; Depends on: odd-part-quotient-by-odd

;;; LEMMA 7 (Lean4: hprod_bound): prod-g(K) ≤ D(0)
;;; Follows from hoddPart_descent since odd-part(D(K)) >= 1

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: THE FINITENESS ARGUMENT SETUP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The Lean4 proof uses a PIGEONHOLE ARGUMENT:
;;;
;;; 1. Assume the "bad" set S = {k | g(k) > 1} is infinite
;;;
;;; 2. Extract D(0)+1 elements from S (possible since S is infinite)
;;;    Let these be indices i_1, i_2, ..., i_{D(0)+1}
;;;
;;; 3. For each bad index i, g(i) ≥ 3 (since gcd of odds, and > 1)
;;;
;;; 4. So product of g over these indices is ≥ 3^{D(0)+1} > D(0)
;;;
;;; 5. But by the oddPart descent, ANY product of g values over
;;;    distinct indices is bounded by odd-part(D(0)) ≤ D(0)
;;;
;;; 6. Contradiction! So S must be finite.
;;;
;;; ACL2 APPROACH (constructive counting):
;;; 
;;; We prove: count-bad(K) < D(0) for all K
;;; 
;;; where count-bad(K) counts bad indices in {0, ..., K-1}.
;;; This directly shows the bad set has < D(0) elements.
;;;
;;; Key lemmas used:
;;; - prod-g(K) >= 3^(count-bad(K))  [each bad g >= 3]
;;; - prod-g(K) <= D(0)              [from hoddPart-descent]
;;; - 3^n > n for all n              [exponential grows faster]
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LEMMA 6 SETUP: hoddPart_descent helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If g is odd and g | 2x, then g | x  
;; Since g is odd, gcd(g,2) = 1, so g | x
(defthm odd-divides-implies-divides-double
  (implies (and (posp g) (integerp x)
                (my-oddp g)
                (dm::divides g (* 2 x)))
           (dm::divides g x))
  :hints (("Goal" :use ((:instance dm::evenp-times (dm::x g) (dm::y (/ (* 2 x) g))))
                  :in-theory (enable dm::divides my-oddp))))

;; D(k+1) = 2 * D(k) / g(k) as an equation
;; Note: Only requires D(k) > 0 since pos-fix handles invalid inputs
(defthm D-recurrence-quotient
  (implies (and (natp k)
                (posp (D-k m0 n0 k)))
           (equal (D-k m0 n0 (1+ k))
                  (/ (* 2 (D-k m0 n0 k))
                     (g-k m0 n0 k))))
  :hints (("Goal" :use ((:instance D-recurrence)))))

;; g(k) | 2*D(k)
(defthm g-divides-2D
  (implies (natp k)
           (dm::divides (g-k m0 n0 k) (* 2 (D-k m0 n0 k))))
  :hints (("Goal" :use ((:instance g-divides-D))
           :in-theory (e/d (dm::divides) (g-divides-D)))))

;; 2*D(k) / g(k) is positive when D(k) > 0
;; Note: Only requires D(k) > 0 since pos-fix handles invalid inputs
(defthm two-D-over-g-posp
  (implies (and (natp k)
                (posp (D-k m0 n0 k)))
           (posp (/ (* 2 (D-k m0 n0 k)) (g-k m0 n0 k))))
  :hints (("Goal" :use ((:instance g-divides-2D)
                        (:instance divides-implies-quotient-posp
                                   (g (g-k m0 n0 k))
                                   (n (* 2 (D-k m0 n0 k))))))))

;; odd-part(D(k+1)) * g(k) = odd-part(D(k))
;; Since D(k+1) = 2*D(k)/g(k) and g(k) is odd, we can use odd-part-quotient-by-odd
;; Note: Only requires D(k) > 0 since pos-fix handles invalid inputs
(defthm oddPart-single-step
  (implies (and (natp k)
                (posp (D-k m0 n0 k)))
           (equal (* (odd-part (D-k m0 n0 (1+ k)))
                     (g-k m0 n0 k))
                  (odd-part (D-k m0 n0 k))))
  :hints (("Goal" :use ((:instance D-recurrence-quotient)
                        (:instance odd-divides-implies-divides-double
                                   (g (g-k m0 n0 k))
                                   (x (D-k m0 n0 k)))
                        (:instance odd-part-times-odd
                                   (n (/ (* 2 (D-k m0 n0 k)) (g-k m0 n0 k)))
                                   (m (g-k m0 n0 k)))
                        (:instance two-D-over-g-posp)
                        (:instance g-k-is-odd)
                        (:instance g-divides-2D))
           :in-theory (disable D-recurrence-quotient odd-divides-implies-divides-double
                               odd-part-times-odd two-D-over-g-posp g-k-is-odd
                               g-divides-2D))))

;; odd-part of a positive integer is positive
(defthm odd-part-of-posp-is-posp
  (implies (posp n)
           (posp (odd-part n)))
  :hints (("Goal" :in-theory (enable odd-part)))
  :rule-classes :type-prescription)

;; D(k) type - always a nat due to abs
(defthm D-k-natp-helper
  (natp (D-k m0 n0 k))
  :hints (("Goal" :in-theory (enable D-k)))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LEMMA 6: hoddPart_descent - The Key Descent Formula
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper: D(k) > 0 implies D(k+1) > 0
;; Note: Only requires D(k) > 0 since pos-fix handles invalid inputs
(defthm D-k-posp-step
  (implies (and (natp k)
                (posp (D-k m0 n0 k)))
           (posp (D-k m0 n0 (1+ k))))
  :hints (("Goal" :use ((:instance D-recurrence-quotient)
                        (:instance two-D-over-g-posp)))))

;; Helper induction scheme for nat induction
(defun nat-induct (k)
  (if (zp k)
      0
    (nat-induct (1- k))))

;; LEMMA 6 (Lean4: hoddPart_descent):
;;   odd-part(D(K)) * prod-g(K) = odd-part(D(0))
;;
;; This is the key formula showing that the product of g values
;; equals the ratio of odd-parts, which bounds the product.
;; Note: Only requires D(0) > 0 since pos-fix handles invalid inputs
(defthm hoddPart-descent
  (implies (and (natp K)
                (posp (D-k m0 n0 0)))
           (equal (* (odd-part (D-k m0 n0 K))
                     (prod-g m0 n0 K))
                  (odd-part (D-k m0 n0 0))))
  :hints (("Goal" :induct (prod-g m0 n0 K)
                  :in-theory (e/d (prod-g) 
                                  (D-k g-k odd-part odd-part-quotient-by-odd)))
          ("Subgoal *1/2" 
           :use ((:instance oddPart-single-step (k (1- K)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LEMMA 6 COROLLARIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; odd-part is at most n (since odd-part divides n)
(defthm odd-part-leq-n
  (implies (posp n)
           (<= (odd-part n) n))
  :hints (("Goal" :in-theory (enable odd-part)))
  :rule-classes :linear)

;; prod-g is positive
(defthm prod-g-posp
  (implies (natp K)
           (posp (prod-g m0 n0 K)))
  :hints (("Goal" :in-theory (enable prod-g)))
  :rule-classes :type-prescription)

;; D(k) is a natural number (integer >= 0)
(defthm D-k-natp
  (implies (and (natp k) (posp m0) (posp n0) (not (equal m0 n0)))
           (natp (D-k m0 n0 k)))
  :hints (("Goal" :in-theory (enable D-k))))

;; D(0) > 0 when m0 ≠ n0
(defthm D-k-0-when-distinct
  (implies (and (posp m0) (posp n0) (not (equal m0 n0)))
           (posp (D-k m0 n0 0)))
  :hints (("Goal" :in-theory (enable D-k))))

;; If x * y = z where y > 0 and z >= 1 and all are integers, then x >= 1
(defthm product-equals-bound
  (implies (and (posp y) (posp z)
                (equal (* x y) z)
                (integerp x))
           (posp x))
  :rule-classes nil)

;; odd-part(D(K)) is positive when D(0) > 0
;; From hoddPart-descent: odd-part(D(K)) * prod-g(K) = odd-part(D(0))
;; prod-g(K) > 0, odd-part(D(0)) >= 1, so odd-part(D(K)) >= 1
(defthm odd-part-D-k-posp
  (implies (and (natp K)
                (posp (D-k m0 n0 0)))
           (posp (odd-part (D-k m0 n0 K))))
  :hints (("Goal" :use ((:instance hoddPart-descent)
                        (:instance product-equals-bound
                                   (x (odd-part (D-k m0 n0 K)))
                                   (y (prod-g m0 n0 K))
                                   (z (odd-part (D-k m0 n0 0))))
                        (:instance prod-g-posp)
                        (:instance odd-part-of-posp-is-posp
                                   (n (D-k m0 n0 0))))
           :in-theory (disable hoddPart-descent prod-g-posp odd-part-of-posp-is-posp))))

;; D(k) > 0 for all k when D(0) > 0
;; Since odd-part(D(K)) >= 1 and D(K) >= odd-part(D(K)), we have D(K) >= 1
(defthm D-k-posp-all
  (implies (and (natp k)
                (posp (D-k m0 n0 0)))
           (posp (D-k m0 n0 k)))
  :hints (("Goal" :use ((:instance odd-part-D-k-posp (K k))
                        (:instance odd-part-leq-n (n (D-k m0 n0 k))))
           :in-theory (disable odd-part-D-k-posp odd-part-leq-n))))

;; If a * b = c and a >= 1 and all positive, then b <= c
(defthm product-bound
  (implies (and (posp a) (posp b) (posp c)
                (equal (* a b) c))
           (<= b c))
  :rule-classes nil)

;; prod-g(K) <= odd-part(D(0))
(defthm prod-g-leq-odd-part-D0
  (implies (and (natp K)
                (posp (D-k m0 n0 0)))
           (<= (prod-g m0 n0 K) (odd-part (D-k m0 n0 0))))
  :hints (("Goal" :use ((:instance hoddPart-descent)
                        (:instance odd-part-D-k-posp)
                        (:instance prod-g-posp)
                        (:instance odd-part-of-posp-is-posp (n (D-k m0 n0 0)))
                        (:instance product-bound
                                   (a (odd-part (D-k m0 n0 K)))
                                   (b (prod-g m0 n0 K))
                                   (c (odd-part (D-k m0 n0 0)))))
           :in-theory (disable hoddPart-descent odd-part-D-k-posp prod-g-posp
                               odd-part-of-posp-is-posp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LEMMA 7: THE MAIN BOUND (Lean4: hprod_g_bound)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LEMMA 7 (final form): prod-g(K) <= D(0)
;; This is crucial for the finiteness argument!
(defthm prod-g-bound
  (implies (and (natp K)
                (posp (D-k m0 n0 0)))
           (<= (prod-g m0 n0 K) (D-k m0 n0 0)))
  :hints (("Goal" :use ((:instance prod-g-leq-odd-part-D0)
                        (:instance odd-part-leq-n (n (D-k m0 n0 0))))
           :in-theory (disable prod-g-leq-odd-part-D0 odd-part-leq-n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; THE FINITENESS ARGUMENT (following Lean4 exactly)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; Lean4 proves: {k | ¬(2*m_k+1).Coprime(2*n_k+1)}.Finite
;;; via contradiction:
;;; 1. Assume infinitely many bad indices
;;; 2. Pick D(0)+1 distinct bad indices  
;;; 3. Product of their g values >= 3^(D(0)+1) > D(0)
;;; 4. But prod-g for any set <= D(0)
;;; 5. Contradiction
;;;
;;; In ACL2, we formulate this as: count-bad(k) < D(0) for all k
;;; which means there are at most D(0)-1 bad indices total.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper: 3^n > n for all n (Lean4: Nat.lt_pow_self)
(defun three-pow (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 1 (* 3 (three-pow (1- n)))))

(defthm three-pow-positive
  (posp (three-pow n))
  :rule-classes :type-prescription)

(defthm three-pow-gt-n
  (implies (natp n)
           (> (three-pow n) n))
  :hints (("Goal" :induct (three-pow n))))

;; Number of bad indices (g > 1) in range 0..k-1
;; Lean4: This is implicit in the |indices| = D(0)+1 argument
(defun count-bad (m0 n0 k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+ (if (> (g-k m0 n0 (1- k)) 1) 1 0)
       (count-bad m0 n0 (1- k)))))

(defthm count-bad-natp
  (natp (count-bad m0 n0 k))
  :rule-classes :type-prescription)

;; Key lemma: prod-g >= 3^(count-bad)
;; Lean4: hprod_ge using Finset.prod_le_prod and hg_ge3'
;; Each bad g(k) >= 3, so product of all g's >= 3^(# of bad indices)

;; Helper: if a <= b and 3 <= c and b,c positive, then 3*a <= c*b
(defthm product-inequality-helper
  (implies (and (<= a b)
                (<= 3 c)
                (posp b)
                (posp c)
                (natp a))
           (<= (* 3 a) (* b c)))
  :hints (("Goal" :nonlinearp t)))

(defthm prod-g-geq-three-pow-count-bad
  (implies (natp k)
           (>= (prod-g m0 n0 k) (three-pow (count-bad m0 n0 k))))
  :hints (("Goal" :induct (count-bad m0 n0 k)
                  :in-theory (enable prod-g count-bad))
          ("Subgoal *1/2" :use ((:instance bad-g-geq-3 (k (1- k)))
                                (:instance product-inequality-helper
                                           (a (three-pow (count-bad m0 n0 (1- k))))
                                           (b (prod-g m0 n0 (1- k)))
                                           (c (g-k m0 n0 (1- k)))))))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MAIN THEOREM: PUTNAM 2025 A1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Lean4's theorem:
;;;   theorem putnam_2025_a1 (m n : ℕ → ℕ)
;;;     (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
;;;     (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
;;;     (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
;;;     {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; LEAN4-MATCHING DEFINITIONS
;;; These mirror the Lean4 definitions exactly

;; Lean4: m, n : ℕ → ℕ  (the sequence functions)
;; In ACL2, m and n are functions of k (with m0, n0 as parameters)
(defmacro m (k) `(m-k m0 n0 ,k))
(defmacro n (k) `(n-k m0 n0 ,k))

;; Lean4: (2 * m k + 1).Coprime (2 * n k + 1)
;; Coprime means gcd = 1
(defun coprime-p (a b)
  "True when gcd(a, b) = 1"
  (equal (dm::gcd a b) 1))

;; Lean4: ¬ (2 * m k + 1).Coprime (2 * n k + 1)
(defun not-coprime-at-k (m0 n0 k)
  "True when gcd(2*m_k+1, 2*n_k+1) ≠ 1, i.e., not coprime"
  (not (coprime-p (+ 1 (* 2 (m-k m0 n0 k)))
                  (+ 1 (* 2 (n-k m0 n0 k))))))

;; Lean4: {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}
;; Count the number of k < K where 2*m_k+1 and 2*n_k+1 are NOT coprime
(defun count-if-not-coprime (m0 n0 K)
  "#{k < K | ¬ Coprime(2*m_k+1, 2*n_k+1)}"
  (count-bad m0 n0 K))

;; Lean4: .Finite means the set has a finite upper bound
;; We express this as: for all K, |{k < K : ¬ Coprime}| < |m(0) - n(0)|

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; THEOREM: putnam_2025_a1
;;;
;;; Lean4:
;;;   theorem putnam_2025_a1 (m n : ℕ → ℕ)
;;;     (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
;;;     (hm : ∀ k, m (k+1) = ((2*m k+1)/(2*n k+1) : ℚ).num)
;;;     (hn : ∀ k, n (k+1) = ((2*m k+1)/(2*n k+1) : ℚ).den):
;;;     {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;;
;;; ACL2 translation:
;;;   Given m0, n0 satisfying h0 (m0 > 0, n0 > 0, m0 ≠ n0),
;;;   with m, n defined by the recurrence (built into m-k, n-k),
;;;   the set {k | ¬ Coprime(2*m(k)+1, 2*n(k)+1)} is finite,
;;;   specifically: |{k < K : not coprime}| < |m0 - n0| for all K.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Main theorem matching Lean4 structure:
;;   theorem putnam_2025_a1 (m n : ℕ → ℕ)
;;     (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
;;     (hm : ∀ k, m (k+1) = ((2*m k+1)/(2*n k+1) : ℚ).num)
;;     (hn : ∀ k, n (k+1) = ((2*m k+1)/(2*n k+1) : ℚ).den):
;;     {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;
;; ACL2 formulation: The number of k where ¬ Coprime(2*m_k+1, 2*n_k+1)
;; is strictly bounded by |m0 - n0|, hence finite.

(defthm putnam_2025_a1
  (implies 
   ;; h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0
   (and (posp m0)                           ; m 0 > 0
        (posp n0)                           ; n 0 > 0
        (not (equal m0 n0))                 ; m 0 ≠ n 0
        (natp K))
   ;; {k | ¬ Coprime(2*m_k+1, 2*n_k+1)}.Finite
   ;; i.e., #{k < K : ¬ Coprime(2*m_k+1, 2*n_k+1)} < |m0 - n0|
   (< (count-if-not-coprime m0 n0 K)        ; #{k < K : gcd ≠ 1}
      (abs (- m0 n0))))                     ; |m(0) - n(0)|
  :hints (("Goal" :use ((:instance prod-g-geq-three-pow-count-bad (k K))
                        (:instance prod-g-bound)
                        (:instance three-pow-gt-n (n (count-bad m0 n0 K)))
                        (:instance D-k-0-when-distinct))
           :in-theory (e/d (D-k count-if-not-coprime) 
                           (prod-g-geq-three-pow-count-bad prod-g-bound
                            three-pow-gt-n D-k-0-when-distinct)))))

