# Copilot Instructions for ACL2-SWF-Experiments

## Project Overview

This repository contains ACL2 theorem prover experiments in two tracks:
1. **Software Foundations** - Adapting proofs from Coq to ACL2 (arithmetic, lists, logic)
2. **Verified Agents** - Formally verified AI agents using ACL2 + Z3 + LangGraph

## Architecture

```
experiments/        # ACL2 proof files organized by topic
  arithmetic/       # Number theorems, Peano encoding
  lists/            # List operations, higher-order functions
  logic/            # (planned) Logical connectives
  agents/           # Verified AI agents with Z3 enforcement
utils/common.lisp   # Shared definitions (add reusable lemmas here)
notes/              # Learning docs, progression tracking
```

## ACL2 File Conventions

- **Package declaration**: Every `.lisp` file starts with `(in-package "ACL2")`
- **File naming**: `experiment-NN-description.lisp` in appropriate subdirectory
- **Helper lemmas**: Wrap with `(local ...)` to prevent export from book
- **Dependencies**: Use `(include-book "path/to/book")` for imports

## Key Build Commands

```bash
# Certify (prove) all ACL2 books
make certify

# Certify a specific book
make experiments/lists/experiment-01-list-basics.cert

# Check which books need certification
make check-cert

# Convert .lisp to Jupyter notebooks
make all

# Clean certification artifacts
make clean-cert
```

## Critical Proof Patterns

### Theory Control (Most Important)

ACL2's rewriter can over-normalize terms. Control it with `:in-theory`:

```lisp
;; Disable a rule globally, re-enable at specific subgoal
:hints (("Goal" :in-theory (e/d (fold-product) (commutativity-of-*)))
        ("Subgoal *1/3''" :in-theory (enable commutativity-of-* associativity-of-*)))
```

See [experiment-02-higher-order-product.lisp](experiments/lists/experiment-02-higher-order-product.lisp) for complete example.

### Avoiding Rewrite Loops

When proving lemmas about the same function, disable earlier lemmas:

```lisp
(defthm revappend-of-append-lists
  (equal (revappend (append x y) acc)
         (revappend y (revappend x acc)))
  :hints (("Goal" :in-theory (disable revappend-is-append-reverse))))
```

### Working with `reverse`

ACL2's `reverse` uses `revappend` internally. Prove helper lemmas about `revappend` first:
1. `append-revappend` - basic interaction
2. `revappend-is-append-reverse` - fundamental characterization  
3. Then prove theorems about `reverse`

See [experiment-01-list-basics.lisp](experiments/lists/experiment-01-list-basics.lisp) for pattern.

## Common Predicates

- `(natp x)` - natural number, `(zp x)` - zero predicate
- `(true-listp l)` - proper list, `(nat-listp l)` - list of naturals
- `(consp x)` - non-empty list, `(endp x)` - end of list

## Development Workflow

1. Write functions and theorems in `.lisp` file
2. Test interactively: run `acl2`, then `(include-book "path/to/book")`
3. If proof fails, check "key checkpoints" in output
4. Add local helper lemmas as stepping stones
5. Run `make experiments/path/to/file.cert` to verify
6. Document insights in [notes/lessons-learned.md](notes/lessons-learned.md)

## Verified Agents Track

The `experiments/agents/` directory contains verified AI agents:

### Architecture Pattern
1. **ACL2 specification** (`.lisp`) - Define state machine, constraints, prove properties
2. **Python notebook** (`.ipynb`) - Runtime implementation with Z3 enforcement

### Permission Model (Orthogonal)
- **File access**: `*access-none*` (0), `*access-read*` (1), `*access-read-write*` (2)
- **Execute**: Separate boolean - tools that run code need execute permission

### Key Functions
```lisp
(tool-permitted-p required-access requires-execute granted-access execute-allowed)
(can-invoke-tool-p st tool)      ; permission AND budget check
(must-respond-p st)              ; budget exhausted or done
(should-continue-p st)           ; has budget AND satisfaction < threshold
```

### Guard Verification
Always verify guards for type safety - this IS the point of verified agents:
```lisp
;; Define return-type theorems for accessors
(defthm agent-iteration-type
  (implies (agent-state-p st)
           (natp (agent-iteration st)))
  :rule-classes :forward-chaining)
```

### LM Studio Integration
Python notebooks connect to LM Studio on host: `http://host.docker.internal:1234/v1`

See [experiment-01-react-verified.lisp](experiments/agents/experiment-01-react-verified.lisp) for ACL2 spec.

## Resources

- [Progression plan](notes/swf-progression-plan.md) - Current roadmap and completed theorems
- [Quick reference](notes/acl2-quick-reference.md) - ACL2 syntax and patterns
- [Lessons learned](notes/lessons-learned.md) - Documented proof techniques
