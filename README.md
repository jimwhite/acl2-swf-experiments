# ACL2 Experiments

A collection of theorem-proving experiments using the [ACL2](https://www.cs.utexas.edu/~moore/acl2/) automated reasoning system. This repository focuses on fundamental theorems from [Software Foundations](https://softwarefoundations.cis.upenn.edu/), adapted from Coq to ACL2.

## Project Goals

- Work through core theorems from Software Foundations Volume 1 (Logical Foundations)
- Explore ACL2's proof automation capabilities
- Document proof techniques and patterns for future reference
- Build a library of reusable lemmas and proof strategies

## Current Progress

**Completed Chapters:**
- ✅ Chapter 2: Basics (arithmetic properties)
- ✅ Chapter 3: Induction (inductive proofs)
- ✅ Chapter 4: Lists (list operations and properties)
- ✅ Chapter 5: Polymorphism (higher-order functions: map, filter, fold)

**Total Theorems Proved:** 50+

See [notes/swf-progression-plan.md](notes/swf-progression-plan.md) for detailed roadmap.

## Structure

```
experiments/
├── arithmetic/     Arithmetic theorems and custom nat encoding
├── lists/         List operations, reverse, append, higher-order functions
├── logic/         (planned) Logical connectives and reasoning
└── data-structures/ (planned) Maps and other data structures

utils/             Shared utility functions and lemmas
notes/             Documentation and lessons learned
```

## Key Proof Techniques Demonstrated

- **Selective Theory Control**: Managing ACL2's rewriter with `:in-theory (e/d ...)`
- **Helper Lemmas**: Building proof support for underlying function definitions (e.g., `revappend`)
- **Avoiding Rewrite Loops**: Strategic use of `:in-theory (disable ...)`
- **Custom Data Structures**: Encoding Peano naturals with correctness proofs

See [notes/lessons-learned.md](notes/lessons-learned.md) for detailed examples.

## Highlighted Experiments

- **[fold-product-append](experiments/lists/experiment-02-higher-order.lisp)**: Proof demonstrating that disabling commutativity can simplify arithmetic reasoning (lines 177-187)
- **[Natural numbers encoding](experiments/arithmetic/experiment-04-natural-numbers.lisp)**: Cons-based Peano naturals with correctness theorems
- **[List reverse theorems](experiments/lists/experiment-01-list-basics.lisp)**: Working with ACL2's `revappend` representation

## Getting Started

### Prerequisites

Install ACL2 (available via Homebrew on macOS, or from source):
```bash
brew install acl2
```

### Running Experiments

Start ACL2 REPL:
```bash
acl2
```

Load an experiment:
```lisp
(include-book "experiments/lists/experiment-01-list-basics")
```

Certify a book (verify all proofs):
```bash
cert.pl experiments/lists/experiment-01-list-basics.lisp
```

## Resources

- [ACL2 Homepage](https://www.cs.utexas.edu/~moore/acl2/)
- [ACL2 Manual](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/)
- [Quick Reference](notes/acl2-quick-reference.md) - Local guide to common ACL2 patterns

## License

BSD 3-Clause License - see [LICENSE](LICENSE) file for details.
