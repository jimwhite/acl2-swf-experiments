# Verified Agent Specification

**Version:** 1.0  
**Date:** December 30, 2025  
**Implementation:** [verified-agent.lisp](../../experiments/agents/verified-agent.lisp)

## Overview

A formally verified ReAct agent implemented in ACL2 with FTY types. The agent's decision logic is proven correct—external tools (knowledge graphs, vector stores, LLMs) are accessed via MCP and treated as oracles with bounded-response axioms.

### Design Philosophy

1. **Verify the decision logic, not the world** — ACL2 proves properties about how the agent decides, given any external responses
2. **FTY over STObj** — Cleaner types, auto-generated theorems, easier reasoning
3. **No SMTLink required** — Pure ACL2 proofs; SMTLink available for future complex numeric properties
4. **MCP for external tools** — Oxigraph (RDF/OWL), Qdrant (vectors), LLMs accessed externally

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Verified Agent (ACL2)                        │
├─────────────────────────────────────────────────────────────────┤
│  Layer 4: Theorems                                              │
│  ├── permission-safety                                          │
│  ├── budget-bounds-after-deduct                                 │
│  ├── termination-by-max-steps                                   │
│  ├── continue-respond-partition                                 │
│  └── state preservation theorems                                │
├─────────────────────────────────────────────────────────────────┤
│  Layer 3: ReAct Loop                                            │
│  ├── react-step (single iteration)                              │
│  └── remaining-steps (termination measure)                      │
├─────────────────────────────────────────────────────────────────┤
│  Layer 2: State Transitions                                     │
│  ├── increment-step, deduct-tool-cost                           │
│  ├── update-satisfaction, mark-done                             │
│  └── set-error                                                  │
├─────────────────────────────────────────────────────────────────┤
│  Layer 1: Pure Decision Functions                               │
│  ├── can-invoke-tool-p (permission + budget)                    │
│  ├── must-respond-p (termination conditions)                    │
│  └── should-continue-p (has budget, not satisfied)              │
├─────────────────────────────────────────────────────────────────┤
│  Layer 0: FTY Types                                             │
│  ├── agent-state, tool-spec, agent-action                       │
│  └── error-kind                                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ encapsulate (external-tool-call)
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    External Tools (MCP)                         │
├─────────────────────────────────────────────────────────────────┤
│  Oxigraph         │  Qdrant           │  LLM                    │
│  (RDF/OWL KG)     │  (Vector Store)   │  (Language Model)       │
│  + Horned-OWL     │                   │                         │
└─────────────────────────────────────────────────────────────────┘
```

---

## Type Definitions

### error-kind (deftagsum)

Structured error states for rich error handling and recovery reasoning.

| Variant | Fields | Purpose |
|---------|--------|---------|
| `:none` | — | No error |
| `:resource-exhausted` | — | Budget depleted |
| `:precondition-failed` | `reason: stringp` | Tool precondition not met |
| `:tool-error` | `tool-name: symbolp`, `message: stringp` | External tool failure |
| `:max-iterations` | — | Step limit reached |

### tool-spec (defprod)

Describes a tool's requirements and costs.

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `name` | `symbolp` | — | Tool identifier |
| `required-access` | `natp` | 0 | File access level (0=none, 1=read, 2=write) |
| `requires-execute` | `booleanp` | nil | Needs code execution permission |
| `token-cost` | `natp` | 0 | Estimated token consumption |
| `time-cost` | `natp` | 0 | Estimated time (seconds) |

### agent-state (defprod)

Core agent state tracking resources, permissions, and status.

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `step-counter` | `natp` | 0 | Current iteration |
| `max-steps` | `natp` | 100 | Maximum allowed iterations |
| `token-budget` | `natp` | 10000 | Remaining token budget |
| `time-budget` | `natp` | 3600 | Remaining time (seconds) |
| `file-access` | `natp` | 0 | Granted file access level |
| `execute-allowed` | `booleanp` | nil | Code execution permitted |
| `satisfaction` | `natp` | 0 | Goal satisfaction (0-100) |
| `done` | `booleanp` | nil | Agent has completed |
| `error-state` | `error-kind-p` | `(:none)` | Current error state |

### agent-action (deftagsum)

Actions the agent can take.

| Variant | Fields | Purpose |
|---------|--------|---------|
| `:tool-call` | `tool-name: symbolp`, `query: stringp` | Invoke external tool |
| `:final-answer` | `answer: stringp` | Return result to user |
| `:no-action` | — | Skip iteration (internal) |

---

## Decision Functions

### Permission Model

```
can-invoke-tool-p = tool-permitted-p ∧ tool-budget-sufficient-p

tool-permitted-p = (required-access ≤ granted-access) 
                 ∧ (¬requires-execute ∨ execute-allowed)

tool-budget-sufficient-p = (token-cost ≤ token-budget) 
                         ∧ (time-cost ≤ time-budget)
```

### Termination Conditions

```
must-respond-p = done 
               ∨ has-error-p 
               ∨ (step-counter ≥ max-steps)
               ∨ (token-budget = 0)
               ∨ (time-budget = 0)

should-continue-p = ¬must-respond-p ∧ (satisfaction < threshold)
```

### State Partition (Proven)

At any point, exactly one of these holds:
1. `must-respond-p` — Agent must stop and respond
2. `should-continue-p` — Agent should take another step
3. `satisfaction ≥ threshold` — Goal achieved

---

## Proven Properties

### Safety Theorems

| Theorem | Statement | Significance |
|---------|-----------|--------------|
| `permission-safety` | `can-invoke-tool-p → tool-permitted-p` | Tool invocation implies permission |
| `budget-bounds-after-deduct` | Budgets remain `natp` after deduction | No negative budgets |
| `error-state-forces-must-respond` | `has-error-p → must-respond-p` | Errors halt processing |

### Termination Theorems

| Theorem | Statement | Significance |
|---------|-----------|--------------|
| `termination-by-max-steps` | `step-counter ≥ max-steps → must-respond-p` | Bounded iterations |
| `step-increases-after-increment` | Step counter strictly increases | Progress guarantee |
| `remaining-steps-decreases-after-increment` | Measure decreases | Termination measure |

### Preservation Theorems

All state transitions preserve `agent-state-p`:
- `deduct-preserves-agent-state`
- `increment-preserves-agent-state`
- `update-satisfaction-preserves-agent-state`
- `mark-done-preserves-agent-state`
- `set-error-preserves-agent-state`
- `react-step-preserves-agent-state`

---

## External Tool Integration

### Encapsulation Strategy

External tools are modeled via ACL2's `encapsulate`:

```lisp
(encapsulate
  (((external-tool-call * *) => *))
  
  ;; Axiom 1: Returns a list
  (defthm external-tool-call-returns-list
    (true-listp (external-tool-call tool-name query)))
  
  ;; Axiom 2: Bounded response
  (defthm external-tool-call-bounded
    (< (len (external-tool-call tool-name query)) 10000)))
```

**Interpretation:** ACL2 proves properties hold for ANY implementation satisfying these axioms. The runtime can use Oxigraph, Qdrant, or any MCP tool—proofs remain valid.

### Planned MCP Tools

| Tool | Type | Purpose | MCP Endpoint |
|------|------|---------|--------------|
| Oxigraph | RDF/OWL KG | Structured knowledge queries | `:kg-oxigraph` |
| Horned-OWL | OWL Reasoner | Ontology reasoning | (via Oxigraph) |
| Qdrant | Vector Store | Similarity search, schema mapping | `:vector-qdrant` |
| LLM | Language Model | Reasoning, generation | `:llm` |

---

## LLM Integration (Phase 1.5)

### Overview

HTTP client integration for LM Studio using the Kestrel `htclient` library (wraps dexador). FTY-typed message structures enable verified reasoning about conversation flow while JSON serialization handles the wire protocol.

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Verified Agent (ACL2)                        │
│  verified-agent.lisp                                            │
│  └── external-tool-call dispatches to llm-chat-completion       │
├─────────────────────────────────────────────────────────────────┤
│                    LLM Client (ACL2)                            │
│  llm-client.lisp                                                │
│  ├── llm-chat-completion (model, messages, state) → response    │
│  ├── Uses FTY chat-message types for verified reasoning         │
│  └── Includes kestrel/htclient for HTTP POST                    │
├─────────────────────────────────────────────────────────────────┤
│                    LLM Types (ACL2)                             │
│  llm-types.lisp                                                 │
│  ├── chat-role (deftagsum: :system, :user, :assistant, :tool)   │
│  ├── chat-message (defprod: role, content)                      │
│  └── chat-message-list (deflist)                                │
├─────────────────────────────────────────────────────────────────┤
│                    Raw Lisp Bridge                              │
│  llm-client-raw.lsp                                             │
│  ├── serialize-chat-message → JSON object                       │
│  ├── serialize-messages → JSON array                            │
│  └── serialize-chat-request → full OpenAI-format body           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ HTTP POST (JSON)
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  LM Studio (host.docker.internal:1234)                          │
│  OpenAI-compatible /v1/chat/completions endpoint                │
└─────────────────────────────────────────────────────────────────┘
```

### LLM Type Definitions

#### chat-role (deftagsum)

| Variant | Purpose |
|---------|---------|
| `:system` | System prompt / instructions |
| `:user` | User input |
| `:assistant` | Model response |
| `:tool` | Tool result (future: MCP integration) |

#### chat-message (defprod)

| Field | Type | Description |
|-------|------|-------------|
| `role` | `chat-role-p` | Message role |
| `content` | `stringp` | Message text |

*Future extension for MCP: add optional `tool-calls` and `tool-call-id` fields*

#### chat-message-list (deflist)

List of `chat-message` for conversation history.

### LLM Client API

```lisp
(define llm-chat-completion
  ((model stringp "Model identifier, e.g., 'local-model'")
   (messages chat-message-list-p "Conversation history")
   state)
  :returns (mv (error "NIL on success or error string")
               (response "Assistant response content" stringp)
               state))
```

### Configuration

| Parameter | Default | Description |
|-----------|---------|-------------|
| `*lm-studio-endpoint*` | `"http://host.docker.internal:1234/v1/chat/completions"` | LM Studio API URL |
| `*llm-connect-timeout*` | 30 | Connection timeout (seconds) |
| `*llm-read-timeout*` | 120 | Read timeout (seconds, higher for slow models) |

### Wire Protocol

**Request (OpenAI format):**
```json
{
  "model": "local-model",
  "messages": [
    {"role": "system", "content": "You are a helpful assistant."},
    {"role": "user", "content": "Hello!"}
  ]
}
```

**Response parsing:** Extract `choices[0].message.content` from JSON response.

### Error Handling

- HTTP 200-299: Success, parse JSON response
- HTTP 4xx/5xx: Return error string with status code
- Connection errors: Return error string with exception message
- JSON parse errors: Return error string with parse failure details

### File Structure

```
experiments/agents/
├── verified-agent.lisp      # Main agent (existing)
├── verified-agent.acl2      # Cert setup (existing)
├── llm-types.lisp           # FTY message types (new)
├── llm-client.lisp          # HTTP client wrapper (new)
├── llm-client-raw.lsp       # JSON serialization (new)
└── llm-client.acl2          # Cert setup with ttags (new)
```

---

## MCP Integration (Phase 1.6 - Planned)

After LLM HTTP integration is working, add MCP tool calls for Oxigraph and Qdrant using the same HTTP/JSON-RPC pattern.

---

## Runtime Architecture (Future)

```
┌─────────────────────────────────────────────────────────────────┐
│                     Python Runtime (optional)                   │
├─────────────────────────────────────────────────────────────────┤
│  LangGraph Orchestration                                        │
│  ├── State management (mirrors ACL2 agent-state)                │
│  ├── Tool dispatch (implements external-tool-call)              │
│  └── Constraint enforcement (Z3 from extracted constraints)     │
├─────────────────────────────────────────────────────────────────┤
│  MCP Tool Clients                                               │
│  ├── oxigraph-mcp (SPARQL queries)                              │
│  ├── qdrant-mcp (vector search)                                 │
│  └── llm-mcp (chat completions)                                 │
└─────────────────────────────────────────────────────────────────┘

Note: With htclient integration, the agent can run entirely in ACL2/SBCL
without Python. Python runtime becomes optional for orchestration.
```

### Constraint Extraction

The decision functions can be extracted to Z3/Python for runtime enforcement:

```python
# Generated from ACL2 can-invoke-tool-p
def can_invoke_tool(tool: ToolSpec, state: AgentState) -> bool:
    permitted = (tool.required_access <= state.file_access and
                 (not tool.requires_execute or state.execute_allowed))
    budget_ok = (tool.token_cost <= state.token_budget and
                 tool.time_cost <= state.time_budget)
    return permitted and budget_ok
```

---

## Future Development

### Phase 2: Goal and Fact Management

Add structured knowledge tracking:

```lisp
(fty::defprod fact
  ((content stringp)
   (source symbolp)      ; :user, :kg, :llm, :inference
   (confidence natp)))   ; 0-100

(fty::deflist fact-list :elt-type fact)

;; Extend agent-state
(fty::defprod agent-state-v2
  ;; ... existing fields ...
  (facts fact-list-p :default nil)
  (goals goal-list-p :default nil))
```

**New theorems to prove:**
- `facts-monotonic` — Facts only grow (never deleted)
- `goal-progress` — Either goal achieved or step taken toward it

### Phase 3: Action History and Audit Trail

```lisp
(fty::defprod action-record
  ((action agent-action-p)
   (step natp)
   (success booleanp)
   (observation stringp)))

(fty::deflist action-history :elt-type action-record)
```

**Properties:**
- Complete audit trail of all decisions
- Enables replay and debugging
- Supports learning from execution

### Phase 4: Multi-Tool Orchestration

```lisp
(fty::defalist tool-registry
  :key-type symbolp
  :val-type tool-spec-p)

(define select-tool ((goal stringp) (registry tool-registry-p) (st agent-state-p))
  :returns (tool tool-spec-p)
  ;; Select best permitted tool for goal
  ...)
```

**Properties:**
- Tool selection respects permissions
- Fallback strategies when preferred tool unavailable

### Phase 5: Learning and Adaptation

- Track tool effectiveness per goal type
- Adjust cost estimates based on observations
- Prove that adaptations preserve safety properties

---

## Testing Strategy

### ACL2 Level
1. **Certification** — `make experiments/agents/verified-agent.cert`
2. **Interactive testing** — ACL2 MCP server for REPL-driven exploration
3. **Theorem coverage** — Ensure key properties have proofs

### Runtime Level
1. **Property-based testing** — Generate random states, verify invariants
2. **Integration tests** — End-to-end with mock MCP tools
3. **Constraint validation** — Compare ACL2 decisions with Z3 decisions

---

## File Structure

```
experiments/agents/
├── verified-agent.lisp      # Main implementation
├── verified-agent.acl2      # Certification setup
├── verified-agent.cert      # Generated certificate
├── llm-types.lisp           # FTY message types (v1.1)
├── llm-client.lisp          # HTTP client wrapper (v1.1)
├── llm-client-raw.lsp       # JSON serialization (v1.1)
├── llm-client.acl2          # Cert setup with ttags (v1.1)
└── (future)
    ├── verified-agent-v2.lisp   # With facts/goals
    ├── mcp-client.lisp          # MCP JSON-RPC client
    └── z3_constraints.py        # Extracted constraints
```

---

## ACL2 Development Patterns

### Guard Verification Strategies

When functions return typed values that callers need to use, ACL2's guard verification can be tricky because it expands function definitions rather than using theorems. Key patterns:

#### 1. Use Type-Prescription Rules

Return-type theorems need `:rule-classes :type-prescription` to be used during guard verification:

```lisp
(defthm natp-of-post-json-status
  (natp (mv-nth 2 (post-json url json-body headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))
```

#### 2. Disable Definitions in Guard Hints

When calling functions with proven return types, disable the definition so ACL2 uses the type-prescription rules instead of expanding:

```lisp
(defun caller (state)
  (declare (xargs :guard-hints (("Goal" :in-theory (disable callee)))))
  (let ((result (callee state)))
    ;; ACL2 now uses natp-of-callee instead of expanding callee
    (process result)))
```

#### 3. Include Standard Library Lemmas

The `std/strings/explode-nonnegative-integer` book provides `character-listp-of-explode-nonnegative-integer`, essential when converting numbers to strings for error messages:

```lisp
(include-book "std/strings/explode-nonnegative-integer" :dir :system)
;; Now (coerce (explode-nonnegative-integer n 10 nil) 'string) verifies guards
```

#### 4. Oracle Pattern for External I/O

For network/file I/O that can't be verified, use `read-acl2-oracle` with proper coercion:

```lisp
(defun external-call (state)
  (mv-let (err val state)
    (read-acl2-oracle state)
    ;; Coerce to expected type for guard satisfaction
    (mv (if (stringp val) val nil)
        (if (natp val) val 0)  ; or (nfix val)
        state)))
```

### Incremental Development with ACL2-MCP

**Always test smaller pieces before integration:**

1. **Test return types** — Define minimal function, prove return-type theorem
2. **Test guard verification** — Write minimal caller, see if guards verify
3. **Identify missing lemmas** — Check which subgoals fail, search books for lemmas
4. **Iterate** — Fix one issue at a time, re-test

Example session pattern:
```lisp
;; In ACL2-MCP session
(defun test-fn (state) ...)
(defthm natp-of-test-fn (natp (mv-nth 1 (test-fn state))) :rule-classes :type-prescription)

;; Test caller
(defun test-caller (state)
  (declare (xargs :guard-hints (("Goal" :in-theory (disable test-fn)))))
  (let ((x (mv-nth 1 (test-fn state))))
    (explode-nonnegative-integer x 10 nil)))  ; Does this verify?
```

### Raw Lisp Bridge Pattern

For functionality requiring Common Lisp features (HTTP, JSON parsing):

```
foo.lisp          -- ACL2 logical definitions with guards
foo-raw.lsp       -- Raw Common Lisp implementations  
foo.acl2          -- Certificate config with :ttags
```

Key points:
- ACL2 definitions are stubs that call `(er hard? ...)`
- Raw definitions replace stubs via `(include-raw "foo-raw.lsp" :host-readtable t)`
- Guard theorems proven on logical definitions still hold
- Break deep nesting into helper functions for maintainability

### Searching the Books

When guard verification fails with "need to prove X about Y", search:

```bash
grep -r "X-of-Y\|Y.*X" /home/acl2/books/std --include="*.lisp" | head -20
```

Common locations:
- `std/strings/` — String and character operations
- `std/lists/` — List operations
- `arithmetic-5/` — Numeric properties
- `centaur/fty/` — FTY-related lemmas

---

## References

- [ACL2 FTY Documentation](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=FTY____FTY)
- [Oxigraph](https://github.com/oxigraph/oxigraph) — RDF graph database
- [Horned-OWL](https://github.com/phillord/horned-owl) — OWL library
- [Qdrant](https://github.com/qdrant/qdrant) — Vector similarity search
- [LangGraph](https://github.com/langchain-ai/langgraph) — Agent orchestration

---

## Changelog

### v1.2 (2025-12-30)
- Added ACL2 Development Patterns section
  - Guard verification strategies (type-prescription, disable hints)
  - Oracle pattern for external I/O
  - Incremental development with ACL2-MCP
  - Raw Lisp bridge pattern
  - Tips for searching the books
- Completed LLM HTTP integration implementation
  - http-json.lisp: Properly-guarded JSON POST
  - llm-client.lisp: LLM API wrapper (certified)
  - All guards verified, no bypassing

### v1.1 (2025-12-30)
- Added LLM HTTP integration plan (Phase 1.5)
- FTY types for chat messages (chat-role, chat-message, chat-message-list)
- HTTP client using Kestrel htclient library
- JSON serialization via raw Lisp bridge
- LM Studio endpoint configuration

### v1.0 (2025-12-30)
- Initial implementation with FTY types
- Core decision functions and state transitions
- Safety and termination theorems
- External tool oracle via encapsulate
- Successful certification
