<img src="https://r2cdn.perplexity.ai/pplx-full-logo-primary-dark%402x.png" style="height:64px;margin-right:32px"/>

# ACL2 Equivalent of Lean4's `Finset.prod`

## Executive Summary

The ACL2 equivalent of Lean4's `Finset.prod` is typically implemented through **fold operations** over finite sets represented as ordered lists. While ACL2's first-order logic requires a different approach than Lean's higher-order `Finset.prod`, the `arithmetic-3` and finite set theory books provide the necessary infrastructure via `foldr`/`foldl` operations or custom recursive functions.

## Lean4's `Finset.prod`: A Brief Recap

In Lean4, `Finset.prod` computes the product of a function applied to each element of a finite set:

```lean
Finset.prod s f = ∏ x ∈ s, f x
```

This higher-order function takes a finite set `s : Finset α` and a function `f : α → β` (where `β` has a multiplicative monoid structure) and returns the product of `f x` for all `x ∈ s`.[^1][^2]

## ACL2's Finite Set Representation

ACL2 represents finite sets as **fully ordered lists**, where order unifies set equality with list equality. The finite set theory book provides:[^3]

- Set recognizer: `setp`
- Membership: `in a X`
- Basic operations: `union`, `intersection`, `difference`
- Quantification mechanisms for bounded quantification over set elements[^3]

This ordered list representation enables efficient O(n) set operations while preserving ACL2's executable nature.

## Primary Equivalent: Fold Operations

### Using `apply$` and Higher-Order Folds

ACL2 supports limited second-order functionality through `apply$`, enabling functional patterns like `foldr`. The product over a set can be expressed as:[^4]

```lisp
;; Using foldr with multiplication
(foldr 'binary-* '1 set-elements)
```

However, `apply$` has constraints: it only works with "tame" functions and requires careful setup.[^4]

### Direct Implementation: `fold-product`

A more practical approach seen in ACL2 practice is defining a specialized product function. The `fold-product` function mentioned in recent ACL2 experiments demonstrates this pattern:[^5]

```lisp
(defun fold-product (lst)
  (if (endp lst)
      1
      (* (car lst) (fold-product (cdr lst)))))
```

This directly mirrors the recursive structure of `Finset.prod` but operates on ACL2's list representation of sets.

## Manual Implementation Strategy

Since ACL2 is first-order, you'll typically define a custom function:

```lisp
;; Step 1: Convert finite set to ordered list
(defun set-to-list (X)
  ;; Implementation depends on your set representation
  ;; For ordered-list sets, this may be the identity
  X)

;; Step 2: Define product over list elements
(defun prod-list (lst)
  (if (atom lst)
      1
      (* (car lst) (prod-list (cdr lst)))))

;; Step 3: Combine for set product
(defun prod-set (X)
  (prod-list (set-to-list X)))
```

For guarded execution with sets:

```lisp
(defun prod-set (X)
  (declare (xargs :guard (setp X)))
  (if (empty X)
      1
      (* (choose X) (prod-set (delete (choose X) X)))))
```


## Key Differences from Lean4

| Aspect | Lean4 `Finset.prod` | ACL2 Equivalent |
| :-- | :-- | :-- |
| **Type System** | Dependent types with `Finset α` | Untyped, lists with `setp` predicate |
| **Higher-Order** | Native higher-order functions | Limited via `apply$` or macro expansion |
| **Execution** | Compiled native code | Direct Common Lisp execution |
| **Reasoning** | Type class inference for monoid | Explicit rewrite rules for `*` and `1` |
| **Set Equality** | Structural equality | Order-sensitive list equality [^3] |

## Recommended Approach

For most ACL2 projects requiring `Finset.prod` functionality:

1. **Use `arithmetic-3` book**: It provides extensive automation for multiplication and simplification[^6][^7]
2. **Define a specialized fold**: Create a custom recursive function rather than using generic folds for better proof automation
3. **Leverage quantification**: Use ACL2's bounded quantification support for reasoning about products[^3]
```lisp
;; Recommended implementation
(include-book "arithmetic-3/top" :dir :system)
(include-book "std/util/define" :dir :system)

(define prod-set ((X setp))
  :returns (product rationalp :rule-classes :type prescription)
  :measure (cardinality X)
  (if (empty X)
      1
      (* (head X) (prod-set (tail X)))))
```

This approach gives you an executable function with strong reasoning support, equivalent to Lean4's `Finset.prod` for finite set multiplication.
<span style="display:none">[^10][^11][^12][^13][^14][^15][^16][^17][^18][^19][^20][^21][^22][^23][^24][^25][^26][^27][^28][^29][^30][^31][^32][^33][^34][^35][^36][^37][^38][^39][^40][^41][^42][^43][^8][^9]</span>

<div align="center">⁂</div>

[^1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Prod.html

[^2]: https://leanprover-community.github.io/mathlib_docs/data/finset/prod.html

[^3]: https://kookamara.com/jared/2004-acl2-set-theory.pdf

[^4]: https://www.cs.utexas.edu/~kaufmann/papers/apply/report.pdf

[^5]: https://mikedodds.org/posts/2025/10/claude-code-acl2-experiments

[^6]: https://www.cs.utexas.edu/~moore/acl2/v6-2/NON-LINEAR-ARITHMETIC.html

[^7]: https://cgi.cse.unsw.edu.au/~eptcs/content.cgi?ACL22023

[^8]: https://cs.brown.edu/courses/cs1951x/static_files/main.pdf

[^9]: https://browncs1951x.github.io/static/files/hitchhikersguide.pdf

[^10]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025/LIPIcs.ITP.2025.pdf

[^11]: https://github.com/bollu/bollu.github.io

[^12]: https://www.ccs.neu.edu/home/cce/acl2/dissertation.pdf

[^13]: https://www.cs.utexas.edu/~moore/publications/finite-set-theory/index.html

[^14]: https://arxiv.org/pdf/2205.11706.pdf

[^15]: https://florisvandoorn.com/LeanCourse24/docs/Mathlib/Data/Finset/Basic.html

[^16]: https://cgi.cse.unsw.edu.au/~eptcs/content.cgi?ACL22020

[^17]: http://www.russinoff.com/papers/groups2.pdf

[^18]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html

[^19]: https://www.cs.utexas.edu/~moore/publications/acl2-books/car/excerpts.pdf

[^20]: https://cgi.cse.unsw.edu.au/~rvg/eptcs/Published/ACL22015/Proceedings.pdf

[^21]: https://www3.risc.jku.at/research/theorema/Groebner-Bases-Bibliography/gbbib_files/publication_913.pos.pdf

[^22]: https://dl.acm.org/doi/pdf/10.1145/1637837.1637840

[^23]: https://www.arith2025.org/proceedings/215900a149.pdf

[^24]: https://www.russinoff.com/papers/groups2.pdf

[^25]: https://www.cs.uwyo.edu/~ruben/static/pdf/nsa.pdf

[^26]: http://www.ccs.neu.edu/home/pete/acl206/papers/cowles.pdf

[^27]: http://www.eecs.uwyo.edu/~ruben/static/pdf/matalg.pdf

[^28]: https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22022.8.pdf

[^29]: https://www.andrew.cmu.edu/user/avigad/Students/lewis_dissertation.pdf

[^30]: https://www.cs.utexas.edu/~moore/acl2/v2-3/acl2-doc-38.html

[^31]: https://stackoverflow.com/questions/27074092/accumulator-in-foldr

[^32]: https://www.cs.utexas.edu/~moore/publications/finite-set-theory/tphols-version.pdf.gz

[^33]: https://www.cs.utexas.edu/~moore/acl2/v6-1/ACL2-BUILT-INS.html

[^34]: https://www2.cs.sfu.ca/CourseCentral/383/tjd/haskell_folding_lhs.html

[^35]: https://www.cs.columbia.edu/~sedwards/classes/2023/4995-fall/recursion.pdf

[^36]: https://argumatronic.com/posts/2016-09-17-infinite-folds.html

[^37]: https://jeapostrophe.github.io/conferences/2013-tfp/proceedings/tfp2013_submission_26.pdf

[^38]: https://en.wikipedia.org/wiki/Fold_(higher-order_function)

[^39]: https://wiki.portal.chalmers.se/cse/uploads/ForMath/lopstr2010-lncs

[^40]: https://cgi.cse.unsw.edu.au/~eptcs/Published/ACL22023/Proceedings.pdf

[^41]: https://www.cs.utexas.edu/~moore/acl2/seminar/2025.04.11-kaufmann/zf.pdf

[^42]: https://nuprl-web.cs.cornell.edu/documents/Caldwell/02acl-nuprl.pdf

[^43]: https://www.cs.utexas.edu/~moore/acl2/v8-6/combined-manual/index.html?topic=ACL2____R-AND-I-ACL2-ARITHMETIC

