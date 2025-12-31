# Copilot Instructions for ACL2-SWF-Experiments

## Project Overview

This repository contains ACL2 theorem prover experiments in two tracks:
1. **Software Foundations** - Adapting proofs from Coq to ACL2 (arithmetic, lists, logic)
2. **Verified Agents** - Formally verified AI agents using ACL2 with FTY types

## Architecture

```
experiments/        # ACL2 proof files organized by topic
  arithmetic/       # Number theorems, Peano encoding
  lists/            # List operations, higher-order functions
  logic/            # (planned) Logical connectives
  agents/           # Verified AI agents - see spec below
utils/common.lisp   # Shared definitions (add reusable lemmas here)
notes/              # Learning docs, progression tracking
acl2-mcp/           # ACL2 MCP server for tool integration
```

## Verified Agents Track (PRIMARY FOCUS)

**IMPORTANT**: When working on verified agents, always consult:
- **[Verified_Agent_Spec.md](experiments/agents/Verified_Agent_Spec.md)** - Complete specification
- **[verified-agent.lisp](experiments/agents/verified-agent.lisp)** - Main implementation

### Core Design Principles

1. **Verify the decision logic, not the world** — ACL2 proves properties about how the agent decides
2. **Keep verified core simple** — Complex operations (LLM, code execution) handled by external driver
3. **FTY over STObj** — Cleaner types, auto-generated theorems, easier reasoning
4. **MCP for external tools** — acl2-mcp provides code execution, future: Oxigraph, Qdrant

### Key Files

| File | Purpose |
|------|---------|
| `verified-agent.lisp` | Main agent: FTY types, decision functions, safety theorems |
| `context-manager.lisp` | Conversation history with sliding window truncation |
| `llm-types.lisp` | FTY message types (chat-role, chat-message) |
| `llm-client.lisp` | HTTP client for LM Studio |
| `Verified_Agent_Spec.md` | **Complete specification - READ THIS FIRST** |

### Permission Model

```lisp
;; File access levels (orthogonal to execute)
*access-none* = 0
*access-read* = 1  
*access-read-write* = 2

;; Decision functions
(tool-permitted-p tool st)        ; permission check
(tool-budget-sufficient-p tool st) ; budget check
(can-invoke-tool-p tool st)       ; permission AND budget
(must-respond-p st)               ; termination conditions
(should-continue-p st)            ; has budget, not satisfied
```

### Proven Safety Properties

- `permission-safety` — `can-invoke-tool-p → tool-permitted-p`
- `budget-bounds-after-deduct` — Budgets remain non-negative
- `termination-by-max-steps` — Agent halts within max-steps
- `truncate-preserves-system-prompt` — System message always preserved

### Code Execution (via acl2-mcp)

Code execution uses **acl2-mcp as external driver** (not ACL2s interface books):
- Agent's `execute-allowed` field controls permission
- External driver extracts code from markdown blocks
- acl2-mcp evaluates code, returns results/errors
- Error messages are useful for LLM learning

### Testing with acl2-mcp

```lisp
;; Use MCP tools for interactive testing
(mcp_acl2-mcp_evaluate :code "(+ 1 2)")           ; => 3
(mcp_acl2-mcp_evaluate :code "(car 5)")           ; => guard violation error
(mcp_acl2-mcp_admit :code "(defun foo (x) x)")    ; test without saving
(mcp_acl2-mcp_prove :code "(defthm ...)")         ; prove theorem
```

## ACL2 File Conventions

- **Package declaration**: Every `.lisp` file starts with `(in-package "ACL2")`
- **File naming**: `experiment-NN-description.lisp` in appropriate subdirectory
- **Helper lemmas**: Wrap with `(local ...)` to prevent export from book
- **Dependencies**: Use `(include-book "path/to/book")` for imports

## Key Build Commands

```bash
# Certify a specific book
cert.pl experiments/agents/verified-agent.lisp

# Or via make
make experiments/agents/verified-agent.cert

# Clean and recertify
rm -f *.cert *.cert.out *.lx64fsl && cert.pl file.lisp
```

## Critical ACL2 Patterns

### FTY Case Macros Require Variables

```lisp
;; WRONG - causes macro expansion error
(chat-role-case (chat-message->role msg) :system ...)

;; CORRECT - bind to variable first
(let ((role (chat-message->role msg)))
  (chat-role-case role :system ...))
```

### Guard Verification with Type-Prescription

```lisp
;; Return-type theorems need :type-prescription for guard verification
(defthm natp-of-my-fn
  (natp (my-fn x))
  :rule-classes (:rewrite :type-prescription))

;; Then disable definition in caller's guard hints
(defun caller (x)
  (declare (xargs :guard-hints (("Goal" :in-theory (disable my-fn)))))
  ...)
```

### Theory Control

```lisp
;; Disable rules that cause loops, enable at specific subgoals
:hints (("Goal" :in-theory (e/d (foo) (bar)))
        ("Subgoal *1/3" :in-theory (enable bar)))
```

## Common Predicates

- `(natp x)` - natural number, `(zp x)` - zero predicate
- `(true-listp l)` - proper list, `(stringp s)` - string
- `(consp x)` - non-empty list, `(endp x)` - end of list
- `(booleanp x)` - boolean, `(symbolp x)` - symbol

## Development Workflow

1. **Read the spec** for verified agents work
2. Write functions and theorems in `.lisp` file
3. Test interactively with acl2-mcp tools
4. If proof fails, check "key checkpoints" in output
5. Add local helper lemmas as stepping stones
6. Run `cert.pl file.lisp` to verify
7. Update spec if design changes

## Resources

- [Verified Agent Spec](experiments/agents/Verified_Agent_Spec.md) - **Primary reference for agents**
- [Progression plan](notes/swf-progression-plan.md) - Roadmap and completed theorems
- [Quick reference](notes/acl2-quick-reference.md) - ACL2 syntax and patterns
- [Lessons learned](notes/lessons-learned.md) - Documented proof techniques

## LM Studio Integration

LLM calls go to LM Studio on host: `http://host.docker.internal:1234/v1`

