# Lessons Learned

## Key Proof Techniques

### Selective Theory Control (fold-product-append)

**Challenge**: Proving `fold-product (append l1 l2) = (* (fold-product l1) (fold-product l2))` failed because ACL2's rewriter normalized arithmetic terms too aggressively, preventing the necessary pattern matching.

**Solution**: Use simple theory control with a Goal-level hint:

```lisp
:hints (("Goal" :in-theory (disable commutativity-of-*)))
```

**Key Insight**:
- This proof fundamentally requires **associativity**, not commutativity
- The inductive step needs to regroup `(* a (* b c))` to `(* (* a b) c)`
- Disabling `commutativity-of-*` prevents the rewriter from normalizing terms into incompatible canonical forms
- With only associativity enabled, the proof completes cleanly (882 vs 2664 prover steps)
- **Avoid subgoal hints when possible** - they are less maintainable than Goal-level hints

**File**: `experiments/lists/experiment-02-higher-order.lisp` (lines 177-187)

### Helper Lemmas for `revappend` (reverse theorems)

**Challenge**: ACL2's `reverse` is defined using `revappend`, requiring helper lemmas about how `revappend` interacts with `append`.

**Solution**: Prove a sequence of helper lemmas with careful theory control:

1. `append-revappend`: Basic property linking append and revappend
2. `revappend-is-append-reverse`: Fundamental characterization
3. `revappend-of-append-lists`: Interaction lemma (with theory disabled to prevent loops)

**Key Insight**: Understanding the underlying definitions is crucial. ACL2 often defines functions in terms of efficient tail-recursive helpers.

**File**: `experiments/lists/experiment-01-list-basics.lisp`

## Common Patterns

### Avoiding Rewrite Loops

When proving lemmas about the same function, use `:in-theory (disable ...)` to prevent previously proved lemmas from interfering:

```lisp
(defthm revappend-of-append-lists
  (equal (revappend (append x y) acc)
         (revappend y (revappend x acc)))
  :hints (("Goal" :in-theory (disable revappend-is-append-reverse))))
```

### Working with Custom Data Structures

When encoding mathematical structures (like Peano naturals), prove correctness theorems linking your encoding to ACL2's built-in operations:

```lisp
(defthm plus*-correct
  (implies (and (natp* n) (natp* m))
           (equal (nat*-to-nat (plus* n m))
                  (+ (nat*-to-nat n) (nat*-to-nat m)))))
```

**File**: `experiments/arithmetic/experiment-04-natural-numbers-correctness.lisp`
