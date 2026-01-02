# ACL2 Experiments

A collection of theorem-proving experiments using the [ACL2](https://www.cs.utexas.edu/~moore/acl2/) automated reasoning system. This repository works through fundamental theorems from [Software Foundations Volume 1: Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/), adapting Coq proofs to ACL2.

## Project Goals

- **Learn by doing**: Work through core theorems from Software Foundations systematically
- **Explore automation**: Understand ACL2's proof automation capabilities and limitations
- **Document techniques**: Build a library of reusable proof patterns and strategies
- **Compare systems**: Understand differences between Coq (constructive) and ACL2 (classical) theorem proving

## Current Progress

**Completed Chapters:**
- ✅ **Chapter 2: Basics** - Arithmetic properties and basic reasoning (10 theorems)
- ✅ **Chapter 3: Induction** - Inductive proofs over natural numbers (6 theorems)
- ✅ **Chapter 4: Lists** - List operations and properties (6 theorems)
- ✅ **Chapter 5: Polymorphism** - Higher-order functions: map, filter, fold (28 theorems)

**Challenge Problems Identified:**
- 🎯 **6 genuine challenges** - 3-4 star SWF exercises requiring non-trivial proof effort
- 📚 **9+ trivial exercises** - SWF "advanced" problems that ACL2 proves automatically

**Total Theorems Proved:** 50+ (plus helper lemmas)

See [notes/swf-progression-plan.md](notes/swf-progression-plan.md) for detailed roadmap and theorem listing.

## Repository Structure

```
experiments/
├── arithmetic/              Chapters 2-3: Natural number theorems
│   ├── experiment-01-hello-world.lisp                  (basic arithmetic)
│   ├── experiment-02-induction-basics.lisp             (commutativity, associativity)
│   ├── experiment-03-basics.lisp                       (distributivity, multiplication)
│   ├── experiment-04-natural-numbers.lisp              (custom Peano encoding)
│   └── experiment-04-natural-numbers-correctness.lisp  (encoding correctness proofs)
├── lists/                   Chapters 4-5: List theorems and higher-order functions
│   ├── experiment-01-list-basics.lisp                  (reverse, append properties)
│   ├── experiment-02-higher-order.lisp                 (map, filter, fold theorems)
│   └── experiment-02-higher-order-product.lisp         (advanced fold theorem)
├── challenge-problems.lisp  6 genuine challenge problems from SWF (3-4 stars)
└── trivial-swf-exercises.lisp  SWF challenges proved automatically by ACL2

utils/common.lisp            Shared utility functions (currently minimal)
notes/                       Documentation and learning resources
```

## Key Experiments Highlighted

### Advanced Proof Techniques

**[fold-product-append](experiments/lists/experiment-02-higher-order-product.lisp)** - Demonstrates selective theory control
```lisp
;; Proving: fold-product(l1 ++ l2) = fold-product(l1) * fold-product(l2)
;; Challenge: ACL2's arithmetic rewriter normalizes too aggressively
;; Solution: Disable commutativity during induction, re-enable strategically
:hints (("Goal" :in-theory (e/d (fold-product) (commutativity-of-*)))
        ("Subgoal *1/3''" :in-theory (enable commutativity-of-* associativity-of-*)))
```

**[List reverse theorems](experiments/lists/experiment-01-list-basics.lisp)** - Working with underlying primitives
```lisp
;; Challenge: reverse is defined as (revappend x nil)
;; Solution: Prove helper lemmas about revappend first
;; Key insight: Understanding ACL2's implementation choices is crucial
```

**[Natural numbers encoding](experiments/arithmetic/experiment-04-natural-numbers.lisp)** - Custom data structures
```lisp
;; Custom Peano naturals using cons pairs
;; Proves correctness theorems linking custom encoding to built-in operations
;; Demonstrates that custom types don't bypass ACL2's automation
```

### ACL2 Automation Power

**[Trivial SWF exercises](experiments/trivial-swf-exercises.lisp)** - Demonstrates what ACL2 solves automatically
- Bag (multiset) operations - 3 theorems, 0 hints needed
- List interleaving - 2 theorems proved instantly
- Peano arithmetic with custom types - Even commutativity is automatic!
- Permutation relation - Reflexivity proved with no guidance

**Key insight**: ACL2's induction heuristics work on ANY structurally recursive definition, not just built-in types. What matters is reasoning complexity, not whether types are built-in.

## Proof Techniques Demonstrated

1. **Selective Theory Control** - Managing ACL2's rewriter with `:in-theory (e/d ...)`
   - Preventing over-normalization while preserving necessary rules
   - Strategic enabling/disabling at specific subgoals

2. **Helper Lemmas** - Building proof support for underlying function definitions
   - Understanding how ACL2 defines functions (e.g., `reverse` via `revappend`)
   - Proving lemmas about primitives before tackling main theorems

3. **Avoiding Rewrite Loops** - Strategic use of `:in-theory (disable ...)`
   - Preventing lemmas from interfering with each other
   - Controlling which rules fire during proof search

4. **Custom Data Structure Correctness** - Encoding mathematical structures
   - Proving correspondence between custom encodings and built-in operations
   - Establishing that custom types preserve desired properties

See [notes/lessons-learned.md](notes/lessons-learned.md) for detailed examples and patterns.

## Getting Started

### Prerequisites

Install ACL2 (version 8.6+ recommended):

**macOS (Homebrew):**
```bash
brew install acl2
```

**From source:**
See [ACL2 installation guide](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/?topic=ACL2____INSTALLATION)

### Running Experiments

**Start ACL2 REPL:**
```bash
acl2
```

**Load an experiment interactively:**
```lisp
ACL2 !>(include-book "experiments/lists/experiment-01-list-basics")
```

**Certify a book (verify all proofs):**
```bash
cert.pl experiments/lists/experiment-01-list-basics.lisp
```

**Run multiple certifications:**
```bash
# Certify all arithmetic experiments
cd experiments/arithmetic
cert.pl experiment-*.lisp
```

### Using with Claude Code

This repository is configured for use with [Claude Code](https://claude.ai/code) and the ACL2 MCP server:

1. The [.claude/settings.json](.claude/settings.json) file pre-approves ACL2 MCP tools
2. Claude Code can directly prove theorems, evaluate expressions, and certify books
3. See [CLAUDE.md](CLAUDE.md) for complete integration details

## Learning Resources

### In This Repository

- **[notes/acl2-quick-reference.md](notes/acl2-quick-reference.md)** - Quick start guide covering:
  - Function definitions and termination
  - Common predicates and patterns
  - Theorem proving basics
  - Debugging failed proofs
  - Advanced techniques (theory control, helper lemmas)

- **[notes/lessons-learned.md](notes/lessons-learned.md)** - Proof techniques discovered:
  - Selective theory control examples
  - Helper lemma patterns
  - Avoiding rewrite loops
  - Working with custom data structures

- **[notes/swf-progression-plan.md](notes/swf-progression-plan.md)** - Complete roadmap:
  - Chapter-by-chapter theorem listing
  - Completed vs. planned work
  - Challenge problem assessment
  - Coq-to-ACL2 concept mapping

### External Resources

- **[ACL2 Homepage](https://www.cs.utexas.edu/~moore/acl2/)** - Official documentation and tutorials
- **[ACL2 Manual](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/)** - Comprehensive reference
- **[Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/)** - Source material (Coq-based)
- **[ACL2 Tutorial](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/ACL2____ACL2-TUTORIAL)** - Interactive learning guide

## Coq vs ACL2: Key Differences

| Aspect | Coq | ACL2 |
|--------|-----|------|
| **Logic** | Constructive (intuitionistic) | Classical |
| **Type System** | Dependent types, polymorphism | First-order logic, no polymorphism |
| **Proof Style** | Interactive tactics | Automated proof search with hints |
| **Automation** | Requires explicit tactics | Aggressive automatic rewriting |
| **Induction** | Manual via `induction` tactic | Automatic induction scheme selection |
| **Functions** | `Fixpoint` with structural recursion | `defun` with termination proof |
| **Theorems** | `Theorem`/`Lemma` with proof script | `defthm` with optional hints |

**Implications:**
- ACL2 can't prove some constructive theorems (no proof-relevant computation)
- ACL2 can't encode polymorphic higher-order functions (Church numerals, currying)
- ACL2 often requires less user guidance (more automation)
- ACL2 requires understanding of rewrite rules and theory control

## Project Status and Next Steps

### Completed Work
- ✅ Core theorems from SWF Chapters 2-5 (50+ theorems)
- ✅ Helper lemma techniques discovered and documented
- ✅ Theory control patterns established
- ✅ Challenge problem assessment complete
- ✅ Automation power demonstrated

### Next Targets
1. **Challenge problems** - Tackle the 6 genuine hard problems in `challenge-problems.lisp`:
   - Binary number system (★★★★ HARD)
   - Function injectivity proofs (★★★☆ MODERATE)

2. **Chapter 7: Logic** - Logical connectives and reasoning
   - Conjunction/disjunction properties
   - De Morgan's laws
   - Classical vs. constructive logic exploration

3. **Chapter 8: Inductively Defined Propositions**
   - Inductive predicates (evenb, regular expressions)
   - Reflexive transitive closure
   - Permutation relation (beyond the trivial reflexivity)

4. **Chapter 9: Total and Partial Maps**
   - Map data structure theorems
   - Functional correctness proofs

### Areas We May Skip
- **Coq-specific tactics** - ACL2 uses a different proof architecture
- **Proof term extraction** - Not applicable in ACL2's model
- **Higher-order function theorems** - Can't be properly encoded without polymorphism

## Contributing

This is a personal learning project, but feedback and suggestions are welcome!

**If you're learning ACL2:**
- The `notes/` directory contains beginner-friendly guides
- Start with `experiments/arithmetic/experiment-01-hello-world.lisp`
- Work through experiments in numerical order within each topic

**If you're experienced with ACL2:**
- Suggestions for better proof techniques are appreciated
- Improvements to documentation welcome
- Alternative proof approaches interesting to discuss

## License

BSD 3-Clause License - see [LICENSE](LICENSE) file for details.

---

**About This Project**: This repository represents a systematic exploration of theorem proving fundamentals through ACL2. Rather than building a single large verified system, it focuses on learning proof techniques through focused experiments. Each file is designed to be readable and educational, with detailed comments explaining proof strategies.
