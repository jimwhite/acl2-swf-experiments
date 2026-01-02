# Claude Code Integration Guide

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Purpose

This repository contains theorem-proving experiments using the ACL2 automated reasoning system. The goal is to explore ACL2's capabilities through focused experiments, working through theorems from Software Foundations Volume 1 (Logical Foundations), adapting Coq proofs to ACL2.

**Current focus**: Chapters 2-5 are complete (50+ theorems proved). Next targets are challenge problems and Chapter 7 (Logic) or Chapter 8 (Inductively Defined Propositions).

**Progress tracking**: See [notes/swf-progression-plan.md](notes/swf-progression-plan.md) for detailed roadmap and status.

## Project Structure

```
certify-all.lisp             Top-level book to verify all experiments build

experiments/
├── arithmetic/              Arithmetic theorems (hello world, induction, basics, natural numbers)
│   ├── experiment-01-hello-world.lisp
│   ├── experiment-02-induction-basics.lisp
│   ├── experiment-03-basics.lisp
│   ├── experiment-04-natural-numbers.lisp
│   └── experiment-04-natural-numbers-correctness.lisp
├── lists/                   List operations (basics, higher-order functions)
│   ├── experiment-01-list-basics.lisp
│   ├── experiment-02-higher-order.lisp
│   └── experiment-02-higher-order-product.lisp
├── logic/                   (planned) Logical connectives and reasoning
├── data-structures/         (planned) Maps and other data structures
├── challenge-problems.lisp  Real 3-4 star challenges from SWF (6 theorems, WIP)
└── trivial-swf-exercises.lisp  SWF challenges that ACL2 proves automatically

utils/
└── common.lisp              Shared utility functions and lemmas (currently minimal)

notes/
├── acl2-quick-reference.md  Concise ACL2 guide for beginners
├── lessons-learned.md       Key proof techniques and patterns discovered
└── swf-progression-plan.md  Complete roadmap and progress tracking

.claude/
└── settings.json            Claude Code permissions for ACL2 MCP tools
```

## Working with ACL2

### ACL2 MCP Server Integration

This repository is configured to use the ACL2 MCP (Model Context Protocol) server with Claude Code. All ACL2 MCP tools are pre-approved in [.claude/settings.json](.claude/settings.json), enabling seamless theorem proving workflows.

**Available MCP operations:**
- Session management: start/end/list sessions
- Code evaluation: evaluate expressions, admit definitions
- Theorem proving: prove theorems with hints, retry failed proofs
- Book operations: certify books, include books
- Query operations: query events, get world state
- Advanced: verify guards, undo, checkpoints

**Usage**: Claude Code can directly use these tools without permission prompts.

### File Conventions

- ACL2 source files use `.lisp` extension
- Files are called "books" in ACL2 terminology
- All ACL2 books must start with `(in-package "ACL2")`
- Mark helper lemmas as `local` if they shouldn't be exported from a book
- Build artifacts (`.cert`, `.fasl`, `.port`, `.out`, `.log`) are git-ignored

### Running ACL2

**Interactive REPL:**
```bash
acl2
```

**Load a book in the REPL:**
```lisp
(include-book "path/to/book")  ; without .lisp extension
```

**Certify a book (verify all proofs):**
```bash
cert.pl path/to/book.lisp
```

**Verify all experiments build successfully:**
```bash
cert.pl certify-all.lisp
```

The `cert.pl` tool is part of the ACL2 installation (typically in `books/build/` within the ACL2 distribution). It automatically certifies dependencies in parallel. The [certify-all.lisp](certify-all.lisp) book at the repository root includes all completed experiments - if it certifies, all theorems are verified.

### Development Workflow for Experiments

1. **Create experiment files** in the appropriate `experiments/` subdirectory
2. **Name files descriptively**: `experiment-NN-description.lisp` for numbered series
3. **Use `include-book`** to load dependencies (though currently experiments are standalone)
4. **Test proofs interactively** in the ACL2 REPL or via MCP before certifying
5. **Document findings** in `notes/lessons-learned.md` for interesting proof techniques
6. **Update progress** in `notes/swf-progression-plan.md` when completing theorems

### Experiment Organization

**By difficulty:**
- **Regular experiments** (`experiments/<topic>/experiment-*.lisp`): Core theorem progression from Software Foundations
- **Challenge problems** (`experiments/challenge-problems.lisp`): 3-4 star SWF exercises requiring non-trivial proof effort
- **Trivial exercises** (`experiments/trivial-swf-exercises.lisp`): SWF challenges that ACL2 solves automatically (demonstrates automation power)

**By topic:**
- **arithmetic/**: Natural number properties, induction, custom Peano encoding
- **lists/**: List operations (reverse, append), higher-order functions (map, filter, fold)
- **logic/**: (planned) Propositional logic, connectives
- **data-structures/**: (planned) Maps, trees

### Shared Utilities

The [utils/common.lisp](utils/common.lisp) file is available for shared definitions used across multiple experiments. Currently minimal as experiments are self-contained, but add reusable lemmas and functions here rather than duplicating them.

## Key Proof Techniques Discovered

See [notes/lessons-learned.md](notes/lessons-learned.md) for detailed examples. Summary:

1. **Selective Theory Control**: Managing ACL2's rewriter with `:in-theory (e/d ...)` to prevent over-normalization
   - Example: `fold-product-append` theorem requires disabling commutativity during induction

2. **Helper Lemmas for Underlying Primitives**: Understanding how ACL2 defines functions
   - Example: `reverse` is defined as `(revappend x nil)`, requiring lemmas about `revappend`

3. **Avoiding Rewrite Loops**: Strategic use of `:in-theory (disable ...)` when lemmas interfere

4. **Custom Data Structure Correctness**: When encoding mathematical structures, prove they correspond to built-in operations
   - Example: Peano naturals with `nat*-to-nat` conversion correctness

## Learning Resources

**Repository documentation:**
- [notes/acl2-quick-reference.md](notes/acl2-quick-reference.md) - Quick start guide covering functions, theorems, lists, and debugging
- [notes/lessons-learned.md](notes/lessons-learned.md) - Proof techniques discovered in this project
- [notes/swf-progression-plan.md](notes/swf-progression-plan.md) - Complete roadmap with chapter status

**External resources:**
- [ACL2 Homepage](https://www.cs.utexas.edu/~moore/acl2/)
- [ACL2 Manual](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/) - Source material

## Important Notes for Claude Code

1. **Experiment files are standalone**: Most don't use `include-book` except for dependencies within the repo
2. **Build artifacts are transient**: `.cert`, `.fasl`, `.port` files are generated by `cert.pl` and git-ignored
3. **Challenge assessment is complete**: All 3-4 star exercises from SWF chapters 2-5 have been audited
   - Only 6 problems in `challenge-problems.lisp` require non-trivial effort
   - Many "advanced" SWF exercises are trivial for ACL2 (documented in `trivial-swf-exercises.lisp`)
4. **Coq vs ACL2 differences**:
   - ACL2 uses classical logic (Coq uses constructive)
   - ACL2 lacks polymorphism (use type-specific functions)
   - ACL2 can't encode higher-order theorems (Church numerals, currying)
5. **Theory control is critical**: ACL2's aggressive rewriter sometimes needs guidance with `:in-theory` hints

## Current Status Summary

- **Chapters completed**: 2 (Basics), 3 (Induction), 4 (Lists), 5 (Polymorphism)
- **Total theorems proved**: 50+ across arithmetic and list domains
- **Challenge problems identified**: 6 theorems requiring non-trivial proof effort
- **Next targets**: Chapter 7 (Logic), Chapter 8 (Inductively Defined Propositions), or challenge problems
- **Repository state**: Well-organized, documented, ready for continued exploration
