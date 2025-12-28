# SMTLink Examples

This folder contains Jupyter notebooks documenting the SMTLink examples from the ACL2 books.

## What is SMTLink?

SMTLink integrates the Z3 SMT solver with ACL2, enabling:
- Non-linear polynomial arithmetic proofs
- Hardware verification with case analysis
- FTY type integration
- Counter-example generation for failed proofs

## Notebooks

| Notebook | Description |
|----------|-------------|
| [01-smtlink-basics.ipynb](01-smtlink-basics.ipynb) | Introduction to SMTLink, basic polynomial inequalities |
| [02-smtlink-expt.ipynb](02-smtlink-expt.ipynb) | Custom Z3 modules for exponentiation |
| [03-smtlink-fty.ipynb](03-smtlink-fty.ipynb) | Using FTY types (defprod, deflist, defalist, defoption) |
| [04-smtlink-hardware.ipynb](04-smtlink-hardware.ipynb) | Ring oscillator verification example |

## Prerequisites

1. **Z3 installed** with Python bindings:
   ```bash
   pip install z3-solver
   ```

2. **SMTLink certified**:
   ```bash
   cd $ACL2_BOOKS/projects/smtlink
   cert.pl top.lisp
   ```

3. **smtlink-config** in `$SMT_HOME` or `$HOME`:
   ```
   smt-cmd=/usr/bin/env python
   ```

## Basic Usage

```lisp
;; Include SMTLink
(include-book "projects/smtlink/top" :dir :system)

;; Enable tshell
(value-triple (tshell-ensure))

;; Add computed hint
(add-default-hints '((SMT::SMT-computed-hint clause)))

;; Use :smtlink hint
(defthm my-theorem
  (implies ...)
  :hints (("Goal" :smtlink nil)))
```

## Source Files

The original SMTLink examples are at:
- `/home/acl2/books/projects/smtlink/examples/`

Key files:
- `examples.lisp` - Main examples (polynomial, FTY, counter-examples)
- `basictypes.lisp` - FTY type definitions  
- `inverter.lisp` - Inverter model for hardware
- `ringosc.lisp` - Ring oscillator verification
- `util.lisp` - Helper FTY types

## Reference

Yan Peng and Mark R. Greenstreet. [Extending ACL2 with SMT Solvers](https://arxiv.org/abs/1509.06082). ACL2 Workshop 2015.
