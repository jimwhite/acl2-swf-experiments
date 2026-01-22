# Lean4 to ACL2 Translation Notes for Putnam 2025 A1

## Summary

The Lean4 proof can be ~80% translated to ACL2. The **blocking issue** is:

> Lean4 uses `Finset.prod g` over an **arbitrary finite set of indices** (the "bad" indices), not just consecutive indices 0..K-1.

ACL2 doesn't have standard machinery for products over arbitrary finite index sets.

## What Translates Directly

### 1. Basic Definitions

**Lean4:**
```lean
let D : ℕ → ℕ := fun k => if m k ≥ n k then m k - n k else n k - m k
let g : ℕ → ℕ := fun k => (2 * m k + 1).gcd (2 * n k + 1)
let oddPart : ℕ → ℕ := fun n => n / 2 ^ n.factorization 2
```

**ACL2 equivalent:**
```lisp
(defun D-k (m0 n0 k)
  (abs (- (m-k m0 n0 k) (n-k m0 n0 k))))

(defun g-k (m0 n0 k)
  (dm::gcd (1+ (* 2 (m-k m0 n0 k))) (1+ (* 2 (n-k m0 n0 k)))))

(defun odd-part (n)
  (if (or (zp n) (oddp n)) n (odd-part (/ n 2))))
```

### 2. Sequence Definition

**Lean4:**
```lean
(hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
(hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den)
```

**ACL2 equivalent:**
```lisp
(defun next-mn (m n)
  (let* ((a (1+ (* 2 m)))
         (b (1+ (* 2 n)))
         (g (dm::gcd a b)))
    (cons (/ a g) (/ b g))))

(defun mn-seq (m0 n0 k)
  (if (zp k) (cons m0 n0)
    (next-mn (car (mn-seq m0 n0 (1- k))) (cdr (mn-seq m0 n0 (1- k))))))
```

### 3. Key Recurrence (Proven by Lean4 as `hD_rec`)

**Lean4:**
```lean
have hD_rec : ∀ k, D (k + 1) * g k = 2 * D k
```

**ACL2:** This can be stated and proven.

### 4. Product Formula (Proven by Lean4 as `hprod_formula`)

**Lean4:**
```lean
have hprod_formula : ∀ K, D K * (Finset.range K).prod g = 2^K * D 0
```

**ACL2:** `Finset.range K` is just `{0, 1, ..., K-1}`, so this translates to:
```lisp
;; D(k) * prod-g(k) = 2^k * D(0)  where prod-g(k) = g(0) * g(1) * ... * g(k-1)
```

### 5. OddPart Descent Formula (Proven by Lean4 as `hoddPart_descent`)

**Lean4:**
```lean
have hoddPart_descent : ∀ K, oddPart (D K) * (Finset.range K).prod g = oddPart (D 0)
```

**ACL2 equivalent:**
```lisp
;; odd-part(D(k)) * prod-g(k) = odd-part(D(0))
```

### 6. Product Bound (Proven by Lean4 as `hprod_bound`)

**Lean4:**
```lean
have hprod_bound : ∀ K, (Finset.range K).prod g ≤ D 0
```

**ACL2:** Follows from oddPart descent since `prod-g(k) ≤ oddPart(D(0)) ≤ D(0)`.

---

## What Does NOT Translate Directly

### 1. The Statement "Set is Finite"

**Lean4:**
```lean
{k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite
```

**Problem:** ACL2 doesn't have a built-in predicate for "the set of natural numbers satisfying P is finite."

**ACL2 equivalent formulation:** "There exists a bound N such that for all k ≥ N, g(k) = 1"

### 2. Products Over Arbitrary Finite Sets

**Lean4:**
```lean
let indices : Finset ℕ := Finset.image (fun i : Fin (D 0 + 1) => (f i).val) Finset.univ
have hprod_ge : 3 ^ (D 0 + 1) ≤ indices.prod g
```

**Problem:** The Lean4 proof picks D(0)+1 arbitrary "bad" indices and takes the product of g over just those indices. ACL2 doesn't have machinery for:
- `Finset.prod` over arbitrary (non-consecutive) finite sets
- Extracting elements from an infinite set (`Set.Infinite.natEmbedding`)

**Key insight:** This is where Lean4's proof uses the **pigeonhole argument**:
- If there are infinitely many bad k, we can pick D(0)+1 of them
- Each bad k has g(k) ≥ 3 (since gcd of odd numbers, and > 1, must be ≥ 3)
- The product of D(0)+1 values each ≥ 3 is at least 3^{D(0)+1} > D(0)
- But the product over *any* subset of indices is bounded by D(0) (from the descent formula)
- Contradiction

### 3. The Contradiction Structure

**Lean4:**
```lean
by_contra hinf
push_neg at hinf
have hSinf : S.Infinite := hinf
... (extract D(0)+1 bad indices, get contradiction)
```

**Problem:** This proof by contradiction about infinite sets doesn't have a direct ACL2 equivalent.

---

## Suggested ACL2 Approach

Instead of proving "the bad set is finite," prove the **constructive equivalent**:

**Theorem:** For all k ≥ `odd-part(D(0))`, we have `g(k) = 1`.

**Proof sketch:**
1. Prove `odd-part(D(k)) * prod-g(k) = odd-part(D(0))` for all k
2. Note that `g(k) | odd-part(D(k))` (since g(k) is odd and g(k) | D(k))
3. When g(k) > 1, we have `odd-part(D(k+1)) < odd-part(D(k))` (strict decrease)
4. Since `odd-part(D(k)) ≥ 1` always, after at most `odd-part(D(0)) - 1` bad steps, we reach `odd-part(D(k)) = 1`
5. When `odd-part(D(k)) = 1`, D(k) is a power of 2, and `g(k) = gcd(odd, odd) dividing power-of-2` implies `g(k) = 1`
6. Once g(k) = 1 at some k0, it stays 1 forever (power-of-2 property is preserved)

**The hard part for ACL2:** Step 4 requires showing that the odd-part decreases at each bad step. The Lean4 proof avoids this by using the pigeonhole argument on arbitrary indices.

---

## Specific Question for ACL2 Expert

The Lean4 proof uses `Finset.prod g` over non-consecutive indices (the "bad" indices). In ACL2:

1. How would you express "the product of g(k) over all k in a finite set S"?

2. How would you prove: "If S is a set of indices where g(k) ≥ 3 for each k ∈ S, and |S| = D(0)+1, then the product of g over S is > D(0)"?

3. The bound uses the oddPart descent: `∏_{i<K} g(i) ≤ oddPart(D(0)) ≤ D(0)`. But this is for *consecutive* indices 0..K-1. The Lean4 proof extends this to products over *any* subset of indices. How would this generalization be stated in ACL2?

The key mathematical insight is that g(k) divides oddPart(D(k)), and oddPart(D(k)) divides oddPart(D(0)), so the product of any collection of g values is bounded by oddPart(D(0)).

## Verified ACL2 Definitions (tested via acl2-mcp)

The following definitions and lemmas have been **verified to work** in ACL2:

```lisp
(include-book "projects/numbers/euclid" :dir :system)  ; for dm::gcd
(include-book "arithmetic-5/top" :dir :system)

;; odd-part: remove all factors of 2
(defun odd-part (n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (not (integerp (/ n 2))))
      n
    (odd-part (/ n 2))))

;; Sequence: m_{k+1}/n_{k+1} = (2*m_k+1)/(2*n_k+1) reduced to lowest terms
(defun next-mn (m n)
  (let* ((a (+ 1 (* 2 m)))
         (b (+ 1 (* 2 n)))
         (g (dm::gcd a b)))
    (cons (/ a g) (/ b g))))

(defun mn-seq (m0 n0 k)
  (declare (xargs :measure (nfix k)))
  (if (zp k) (cons m0 n0)
    (next-mn (car (mn-seq m0 n0 (1- k))) (cdr (mn-seq m0 n0 (1- k))))))

(defun m-k (m0 n0 k) (car (mn-seq m0 n0 k)))
(defun n-k (m0 n0 k) (cdr (mn-seq m0 n0 k)))
(defun g-k (m0 n0 k)
  (dm::gcd (+ 1 (* 2 (m-k m0 n0 k))) (+ 1 (* 2 (n-k m0 n0 k)))))
(defun D-k (m0 n0 k)
  (abs (- (m-k m0 n0 k) (n-k m0 n0 k))))
(defun prod-g (m0 n0 k)   ; product of g(0)..g(k-1)
  (declare (xargs :measure (nfix k)))
  (if (zp k) 1 (* (g-k m0 n0 (1- k)) (prod-g m0 n0 (1- k)))))

;; Proven lemmas (all certified in putnam-2025-a1-lean-translation.lisp):

;; Bridge lemmas connecting dm::gcd to integerp
(defthm divides-means-integerp-quotient
  (implies (dm::divides d a) (integerp (/ a d))))
(defthm gcd-divides-first
  (implies (and (integerp a) (integerp b) (not (= a 0)))
           (dm::divides (dm::gcd a b) a)))
(defthm quotient-by-gcd-integerp
  (implies (and (integerp a) (integerp b) (not (= a 0)))
           (integerp (/ a (dm::gcd a b)))))
(defthm gcd-posp
  (implies (and (posp a) (posp b)) (posp (dm::gcd a b)))
  :rule-classes :type-prescription)
(defthm quotient-by-gcd-posp
  (implies (and (posp a) (posp b)) (posp (/ a (dm::gcd a b))))
  :rule-classes :type-prescription)

;; Type properties for odd-part
(defthm odd-part-posp (implies (posp n) (posp (odd-part n))))
(defthm odd-part-leq (implies (posp n) (<= (odd-part n) n)))

;; Type properties for next-mn (KEY - needed for mn-seq induction)
(defthm next-mn-car-posp (posp (car (next-mn m n))) :rule-classes :type-prescription)
(defthm next-mn-cdr-posp (posp (cdr (next-mn m n))) :rule-classes :type-prescription)

;; Type properties for mn-seq (proved by SIMULTANEOUS INDUCTION)
;; The key insight: prove car and cdr together in single induction
(defthm mn-seq-posp-pair
  (and (posp (car (mn-seq m0 n0 k)))
       (posp (cdr (mn-seq m0 n0 k))))
  :rule-classes ((:type-prescription :corollary (posp (car (mn-seq m0 n0 k))))
                 (:type-prescription :corollary (posp (cdr (mn-seq m0 n0 k))))))

;; Accessor type rules (derived)
(defthm m-k-posp (posp (m-k m0 n0 k)) :rule-classes :type-prescription)
(defthm n-k-posp (posp (n-k m0 n0 k)) :rule-classes :type-prescription)
```

## Key Recurrences (PROVEN)

These lemmas have been formally proven in `putnam-2025-a1-lean-translation.lisp`:

1. **D-recurrence** ✅: `D(k+1) * g(k) = 2 * D(k)`
   ```lisp
   (defthm D-recurrence
     (implies (natp k)
              (equal (* (D-k m0 n0 (+ 1 k)) (g-k m0 n0 k))
                     (* 2 (D-k m0 n0 k)))))
   ```

2. **Product formula** ✅: `D(K) * prod-g(K) = 2^K * D(0)`
   ```lisp
   (defthm product-formula
     (implies (natp k)
              (equal (* (D-k m0 n0 k) (prod-g m0 n0 k))
                     (* (expt 2 k) (D-k m0 n0 0)))))
   ```

3. **OddPart descent** (NOT YET PROVEN): `odd-part(D(K)) * prod-g(K) = odd-part(D(0))`

4. **Product bound** (NOT YET PROVEN): `prod-g(K) ≤ D(0)`

## The Blocking Issue (Detailed)

The Lean4 proof structure is:

```lean
-- Assume bad set S = {k | g(k) > 1} is infinite
by_contra hinf
have hSinf : S.Infinite := hinf

-- Extract D(0)+1 bad indices
let f := Set.Infinite.natEmbedding S hSinf
let indices : Finset ℕ := Finset.image (fun i : Fin (D 0 + 1) => (f i).val) Finset.univ

-- Product over these D(0)+1 indices, each g ≥ 3
have hprod_ge : 3 ^ (D 0 + 1) ≤ indices.prod g

-- But any product of g values ≤ D(0) (from oddPart descent)
have h_final : indices.prod g ≤ D 0

-- Contradiction: 3^{D(0)+1} > D(0)
```

The issue is `indices.prod g` where `indices` is an **arbitrary subset** of ℕ, not {0,1,...,K-1}.

**In ACL2 terms, we need:**

1. A way to represent a finite set of natural numbers (maybe as a sorted list?)
2. `(prod-g-over-list m0 n0 indices)` = product of g(k) for k in indices
3. Prove: for any finite set of indices, this product ≤ D(0)

The bound follows from:
- Each g(k) divides odd-part(D(k))
- odd-part(D(k)) divides odd-part(D(0)) (by the descent formula)
- So product of g values over any indices divides odd-part(D(0)) ≤ D(0)

**Question**: What's the standard ACL2 idiom for "product over a finite set of indices"?

---

## Update: Finset.prod Approach Implemented

Based on the "ACL2 Equivalent of Lean4's Finset.prod" recommendations, I've created:

**[putnam-2025-a1-finset-approach.lisp](putnam-2025-a1-finset-approach.lisp)** - Certifies successfully!

### Key Implementation

```lisp
;; Product over arbitrary list of indices (Finset.prod equivalent)
(defun prod-g-over-list (m0 n0 indices)
  "Product of g(k) for each k in indices"
  (if (atom indices)
      1
    (* (g-k m0 n0 (car indices))
       (prod-g-over-list m0 n0 (cdr indices)))))
```

### Remaining Work

The file has the structure but these lemmas still need proofs:

1. **D-recurrence**: `D(k+1) * g(k) = 2 * D(k)`
2. **oddpart-descent**: `odd-part(D(K)) * prod-g(K) = odd-part(D(0))`
3. **prod-g-over-list-bounded**: `prod-g-over-list(indices) <= D(0)` for any finite index list
4. **bad-g-geq-3**: `g(k) > 1` implies `g(k) >= 3`
5. **putnam-2025-a1**: For `k >= bound-N`, `g(k) = 1`

The proof structure follows the Lean4 contradiction argument:
- If there were D(0)+1 bad indices, their g-product would be ≥ 3^{D(0)+1}
- But any g-product is bounded by D(0)
- Since 3^{D(0)+1} > D(0), contradiction
