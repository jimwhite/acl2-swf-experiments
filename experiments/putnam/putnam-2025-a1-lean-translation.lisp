;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; putnam-2025-a1-lean-translation.lisp
;;;
;;; Direct translation of Lean4 Putnam 2025 A1 definitions to ACL2.
;;; 
;;; STATUS: Definitions work. Key lemmas can be proven.
;;;         Main theorem needs ACL2 expert guidance (see notes at end).
;;;
;;; The Lean4 theorem statement is:
;;;   {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
;;;
;;; ACL2 equivalent would be:
;;;   There exists bound N such that for all k >= N, gcd(2*m_k+1, 2*n_k+1) = 1
;;;
;;; Author: Claude (translation from Lean4)
;;; Date: January 2026
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; For dm::gcd and dm::divides
(include-book "projects/numbers/euclid" :dir :system)

;; For arithmetic
(include-book "arithmetic-5/top" :dir :system)

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
;;; PART 5: KEY LEMMAS FROM LEAN4 (TO BE PROVEN)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; LEMMA 1 (Lean4: hne): m_k ≠ n_k for all k
;;; (defthm mn-seq-distinct ...)

;;; LEMMA 2 (Lean4: hg_odd): g(k) is odd for all k
;;; (Since gcd of two odd numbers is odd)

;;; LEMMA 3 (Lean4: hg_dvd_D): g(k) | D(k)
;;; (The gcd divides the absolute difference)

;;; LEMMA 4 (Lean4: hD_rec): D(k+1) * g(k) = 2 * D(k)
;;; KEY RECURRENCE

;;; LEMMA 5 (Lean4: hprod_formula): D(K) * prod-g(K) = 2^K * D(0)

;;; LEMMA 6 (Lean4: hoddPart_descent): 
;;;   odd-part(D(K)) * prod-g(K) = odd-part(D(0))

;;; LEMMA 7 (Lean4: hprod_bound): prod-g(K) ≤ D(0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART 6: THE CHALLENGE - WHAT LEAN4 DOES THAT'S HARD IN ACL2
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
;;; THE PROBLEM FOR ACL2:
;;; - ACL2 doesn't have Finset.prod over arbitrary index sets
;;; - ACL2 doesn't have Set.Infinite or Set.Finite predicates
;;; - The bound "product over ANY subset ≤ D(0)" needs careful statement
;;;
;;; ALTERNATIVE APPROACH (constructive):
;;; 
;;; Instead of contradiction, prove directly:
;;;   For all k >= odd-part(D(0)), g(k) = 1
;;;
;;; This requires showing that odd-part(D(k)) strictly decreases
;;; at each "bad" step until it reaches 1.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; QUESTION FOR ACL2 EXPERT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The key mathematical fact from Lean4 is:
;;;
;;;   "The product of g(i) over ANY finite set of distinct indices
;;;    is bounded by odd-part(D(0)) ≤ D(0)"
;;;
;;; This follows because:
;;;   - g(i) | odd-part(D(i))  (g is odd and divides D)
;;;   - odd-part(D(i)) | odd-part(D(0)) for all i (by the descent formula)
;;;   - So the product of any distinct g values divides odd-part(D(0))
;;;
;;; How would you state and prove this bound in ACL2?
;;;
;;; Specifically, we need something like:
;;;
;;; (defthm product-of-distinct-gs-bounded
;;;   (implies (and (posp m0) (posp n0) (not (= m0 n0))
;;;                 (distinct-index-list indices)
;;;                 (all-indices-natp indices))
;;;            (<= (product-of-g-over-list m0 n0 indices)
;;;                (D-k m0 n0 0))))
;;;
;;; Where product-of-g-over-list computes g(i_1) * g(i_2) * ... * g(i_n)
;;; for the indices in the list.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
