# Verified Agent Specification

**Version:** 1.5  
**Date:** December 31, 2025  
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
│  Layer 5: Theorems                                              │
│  ├── permission-safety, budget-bounds-after-deduct              │
│  ├── termination-by-max-steps, continue-respond-partition       │
│  ├── conversation preservation theorems                         │
│  └── truncate-preserves-system-prompt                           │
├─────────────────────────────────────────────────────────────────┤
│  Layer 4: ReAct Loop with Conversation                          │
│  ├── react-step (single iteration)                              │
│  ├── react-step-with-conversation (state + messages)            │
│  └── remaining-steps (termination measure)                      │
├─────────────────────────────────────────────────────────────────┤
│  Layer 3: State Transitions                                     │
│  ├── increment-step, deduct-tool-cost                           │
│  ├── update-satisfaction, mark-done, set-error                  │
│  └── add-user-msg, add-assistant-msg, add-tool-result           │
├─────────────────────────────────────────────────────────────────┤
│  Layer 2: Context Management (context-manager.lisp)             │
│  ├── Token estimation (4 chars/token conservative)              │
│  ├── truncate-to-fit (sliding window, preserves system)         │
│  ├── truncate-output (head+tail for tool results)               │
│  └── add-message with automatic truncation                      │
├─────────────────────────────────────────────────────────────────┤
│  Layer 1: Pure Decision Functions                               │
│  ├── can-invoke-tool-p (permission + budget)                    │
│  ├── must-respond-p (termination conditions)                    │
│  └── should-continue-p (has budget, not satisfied)              │
├─────────────────────────────────────────────────────────────────┤
│  Layer 0: FTY Types                                             │
│  ├── agent-state, tool-spec, agent-action, error-kind           │
│  └── chat-role, chat-message, chat-message-list                 │
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
| `messages` | `chat-message-list-p` | nil | Conversation history |
| `max-context-tokens` | `natp` | 8000 | Context window limit |
| `system-prompt` | `stringp` | "" | System prompt text |

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
- `init-agent-conversation-preserves-agent-state`
- `add-user-msg-preserves-agent-state`
- `add-assistant-msg-preserves-agent-state`
- `add-tool-result-preserves-agent-state`
- `react-step-with-conversation-preserves-agent-state`

### Conversation Preservation Theorems

Adding messages only changes the `:messages` field, preserving control flow:
- `add-assistant-msg-preserves-must-respond-p` — Conversation doesn't affect termination
- `add-assistant-msg-preserves-has-error-p` — Error state unchanged
- `add-tool-result-preserves-has-error-p` — Tool results don't affect errors
- All field-level preservation: `done`, `error-state`, `step-counter`, `max-steps`, `token-budget`, `time-budget`

### Context Management Theorems (context-manager.lisp)

| Theorem | Statement | Significance |
|---------|-----------|---------------|
| `truncate-preserves-system-prompt` | System message always preserved after truncation | LLM always gets instructions |
| `truncate-to-fit-length-bound` | Truncated ≤ original length | Truncation reduces, never grows |
| `chat-message-list-p-of-append` | Append preserves message list type | Type safety for message building |

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

## Context Management (Phase 1.6)

### Overview

Verified context length management following mini-swe-agent's pattern but with ACL2 formal verification. Ensures conversation history fits in model context windows with system prompt always preserved.

### Design Principles (from mini-swe-agent)

1. **Simple list-based storage** — Messages stored as `chat-message-list`
2. **Sliding window truncation** — Drop oldest non-system messages when context full
3. **System prompt preservation** — First message (system) always kept
4. **Output truncation** — Large tool outputs use head+tail strategy
5. **Conservative estimation** — 4 chars/token avoids context overflow

### Constants

| Constant | Value | Purpose |
|----------|-------|---------|
| `*chars-per-token*` | 4 | Conservative token estimation |
| `*context-safety-margin*` | 500 | Reserved tokens for response |
| `*output-head-chars*` | 5000 | Tool output head portion |
| `*output-tail-chars*` | 5000 | Tool output tail portion |
| `*output-max-chars*` | 10000 | Total output truncation limit |

### Core Functions

#### Token Estimation

```lisp
(define estimate-tokens ((chars natp))
  :returns (tokens natp)
  ;; Ceiling division: (chars + 3) / 4
  (nfix (truncate (+ chars 3) 4)))

(define messages-token-estimate ((msgs chat-message-list-p))
  :returns (tokens natp)
  (estimate-tokens (messages-char-length msgs)))
```

#### Context Fitting

```lisp
(define messages-fit-p ((msgs chat-message-list-p) (max-tokens natp))
  :returns (result booleanp)
  (b* ((used (messages-token-estimate msgs))
       (available (nfix (- max-tokens *context-safety-margin*))))
    (<= used available)))
```

#### Sliding Window Truncation

```lisp
(define truncate-to-fit ((msgs chat-message-list-p) (max-tokens natp))
  :returns (truncated chat-message-list-p)
  ;; Preserves first message (system prompt)
  ;; Drops oldest non-system messages until fit
  (b* ((sys-msg (extract-system-message msgs))
       (rest (non-system-messages msgs))
       (trimmed (drop-oldest-until-fit rest max-tokens sys-msg)))
    (if sys-msg
        (cons sys-msg trimmed)
      trimmed)))
```

#### Output Truncation (mini-swe-agent pattern)

```lisp
(define truncate-output ((output stringp) (max-chars natp))
  :returns (truncated stringp)
  ;; Head + "..." + tail when output exceeds max
  (b* ((len (length output)))
    (if (<= len max-chars)
        output
      (b* ((head-size (nfix (truncate max-chars 2)))
           (tail-size (nfix (- (nfix (- max-chars head-size)) 5)))
           (head (subseq output 0 head-size))
           (tail (subseq output (nfix (- len tail-size)) len)))
        (concatenate 'string head "
... output truncated ...
" tail)))))
```

### Agent-Level Conversation Functions

```lisp
;; Initialize conversation with system prompt
(define init-agent-conversation ((system-prompt stringp) (st agent-state-p))
  :returns (new-st agent-state-p))

;; Add messages with auto-truncation
(define add-user-msg ((content stringp) (st agent-state-p))
  :returns (new-st agent-state-p))

(define add-assistant-msg ((content stringp) (st agent-state-p))
  :returns (new-st agent-state-p))

(define add-tool-result ((content stringp) (st agent-state-p))
  :returns (new-st agent-state-p))  ; auto-truncates output

;; ReAct step with conversation management
(define react-step-with-conversation
  ((action agent-action-p)
   (tool tool-spec-p)
   (assistant-msg stringp)    ; LLM response
   (tool-result stringp)      ; Tool output
   (st agent-state-p))
  :returns (new-st agent-state-p)
  :guard (not (must-respond-p st)))
```

### Key Theorems

```lisp
;; System prompt always preserved during truncation
(defthm truncate-preserves-system-prompt
  (implies (and (chat-message-list-p msgs)
                (natp max-tokens)
                (first-is-system-p msgs))
           (first-is-system-p (truncate-to-fit msgs max-tokens))))

;; Truncation never increases message count
(defthm truncate-to-fit-length-bound
  (implies (chat-message-list-p msgs)
           (<= (len (truncate-to-fit msgs max-tokens))
               (len msgs))))

;; Conversation changes don't affect agent control flow
(defthm add-assistant-msg-preserves-must-respond-p
  (equal (must-respond-p (add-assistant-msg content st))
         (must-respond-p st)))
```

---

## Code Execution (Phase 1.8)

### Overview

Code execution enables the verified agent to run ACL2 expressions provided by the LLM. We use **acl2-mcp as an external driver** rather than calling ACL2s interface books from within ACL2. This keeps the verified core simple and inspectable.

### Design Principles

1. **External driver, verified permissions** — acl2-mcp handles execution, ACL2 controls permission
2. **Keep verified core simple** — No complex parsing/execution code in certified books
3. **MCP is already needed** — We want MCP tool support anyway; this is a natural fit
4. **Useful error messages** — ACL2 provides clear guard violations, undefined symbols, syntax errors

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Verified Agent (ACL2)                        │
│  verified-agent.lisp                                            │
│  ├── execute-allowed field controls permission                  │
│  ├── tool-permitted-p checks execute permission                 │
│  └── can-invoke-tool-p gates tool invocation                    │
├─────────────────────────────────────────────────────────────────┤
│                    External Driver (Python/MCP Client)          │
│  ├── Extracts code from ```acl2 and ```lisp markdown blocks     │
│  ├── Checks agent state for execute permission                  │
│  ├── Calls acl2-mcp to evaluate code                            │
│  └── Formats result/error for LLM consumption                   │
├─────────────────────────────────────────────────────────────────┤
│                    acl2-mcp (MCP Server)                        │
│  ├── mcp_acl2-mcp_evaluate - Single expressions                 │
│  ├── mcp_acl2-mcp_admit - Test without saving                   │
│  ├── mcp_acl2-mcp_prove - Theorem proving                       │
│  └── Sessions for stateful development                          │
└─────────────────────────────────────────────────────────────────┘
```

### Why External Driver (not ACL2s books)?

The `acl2s-compute`, `acl2s-query`, and `acl2s-event` functions from `acl2s/interface/top` are designed for **Common Lisp programs calling into ACL2** (e.g., ACL2s IDE, raw Lisp mode). They are not meant to be called from certified ACL2 books.

Benefits of external driver approach:
- **Simpler verified core** — Easier to inspect and trust
- **Already have acl2-mcp** — No new code needed for execution
- **Better error messages** — acl2-mcp captures full ACL2 output
- **MCP ecosystem** — Same pattern for future tools (Oxigraph, Qdrant)

### acl2-mcp Error Messages (Tested)

| Input | Error Message |
|-------|---------------|
| `(+ 1 2)` | Returns `3` ✓ |
| `(+ 1 'bad)` | "The guard `(AND (ACL2-NUMBERP X) (ACL2-NUMBERP Y))` is violated by `(BINARY-+ 1 'BAD)`" |
| `(undefined-fn 1 2)` | "The symbol `UNDEFINED-FN` has neither a function nor macro definition in ACL2. Please define it." |
| `(car 5)` | "The guard `(OR (CONSP X) (EQUAL X NIL))` is violated by `(CAR 5)`" |
| `((nested (wrong)))` | "Function applications must begin with a symbol or LAMBDA expression" |
| `(let ((x 1) (y)) x)` | "The proper form of a let is `(let bindings dcl ... dcl body)` where bindings has the form `((v1 term) ...)`" |
| `(+ 1 2` | "end of file" (incomplete parens) |

These messages are clear enough for an LLM to learn from its mistakes.

### External Driver Implementation

The external driver (Python or orchestration layer) handles:

```python
# Pseudocode for external driver
def execute_acl2_code(agent_state, llm_response):
    # 1. Check permission in verified state
    if not agent_state.execute_allowed:
        return "Error: Code execution not permitted"
    
    # 2. Extract code blocks from markdown
    code_blocks = extract_code_blocks(llm_response)  # ```acl2 or ```lisp
    
    # 3. Execute via acl2-mcp
    results = []
    for code in code_blocks:
        result = mcp_acl2_evaluate(code)
        results.append(format_result(result))
    
    # 4. Return formatted results for LLM
    return "\n".join(results)

def extract_code_blocks(text):
    """Find ```acl2 and ```lisp fenced blocks"""
    # ... regex or simple parsing ...
    
def format_result(mcp_result):
    """Format for LLM consumption"""
    if "Error" in mcp_result:
        return f"Error: {extract_error_message(mcp_result)}"
    else:
        return f"Result: {extract_value(mcp_result)}"
```

### Tool Specification (in verified-agent.lisp)

```lisp
(defconst *acl2-compute-tool*
  (make-tool-spec
    :name 'acl2-compute
    :required-access 0        ; No file access needed
    :requires-execute t       ; Requires execute permission
    :token-cost 200           ; Budget for result
    :time-cost 10))           ; 10 second typical
```

### Integration with Verified Agent

The agent's `execute-allowed` field gates code execution:

```lisp
;; In verified-agent.lisp - already proven
(define tool-permitted-p ((tool tool-spec-p) (st agent-state-p))
  :returns (result booleanp)
  (b* ((required-access (tool-spec->required-access tool))
       (requires-exec (tool-spec->requires-execute tool))
       (granted-access (agent-state->file-access st))
       (exec-allowed (agent-state->execute-allowed st)))
    (and (access-sufficient-p required-access granted-access)
         (or (not requires-exec) exec-allowed))))  ; <-- execute check

;; Theorem: can-invoke implies permitted (already proven)
(defthm permission-safety
  (implies (can-invoke-tool-p tool st)
           (tool-permitted-p tool st)))
```

### Files to Clean Up

- **DELETE** `code-exec.lisp` — No longer needed; execution is external
- **DELETE** `code-exec.acl2` — No longer needed
- **DELETE** `code-exec-demo.lisp` — No longer needed
- **KEEP** The tool spec constant can go in `verified-agent.lisp`

### Testing Code Execution

Use acl2-mcp directly:

```
# Via MCP tools in Copilot/Claude
mcp_acl2-mcp_evaluate :code "(+ 1 2)"
mcp_acl2-mcp_evaluate :code "(append '(1 2) '(3 4))"
mcp_acl2-mcp_evaluate :code "(car 5)"  ; test error handling

# For stateful work (defuns that build on each other)
mcp_acl2-mcp_start_session :name "agent-test"
mcp_acl2-mcp_evaluate :session_id "..." :code "(defun foo (x) (+ x 1))"
mcp_acl2-mcp_evaluate :session_id "..." :code "(foo 5)"
```

---

## MCP Client (ACL2 HTTP Client for acl2-mcp)

### Overview

The MCP client enables the verified agent to call acl2-mcp tools directly from ACL2 via HTTP. This provides an alternative to the external Python driver approach—the agent can execute code without leaving ACL2.

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Verified Agent (ACL2)                        │
│  verified-agent.lisp                                            │
│  └── Calls mcp-acl2-evaluate, mcp-acl2-admit, mcp-acl2-prove    │
├─────────────────────────────────────────────────────────────────┤
│                    MCP Client (ACL2)                            │
│  mcp-client.lisp                                                │
│  ├── mcp-connect (endpoint, state) → (err, conn, state)         │
│  ├── mcp-call-tool (conn, tool, args, state) → (err, result)    │
│  ├── mcp-acl2-evaluate (conn, code, state) → (err, result)      │
│  ├── mcp-acl2-admit (conn, code, state) → (err, result)         │
│  └── mcp-acl2-prove (conn, code, state) → (err, result)         │
├─────────────────────────────────────────────────────────────────┤
│                    HTTP Client (ACL2)                           │
│  http-json.lisp (wraps dexador via quicklisp)                   │
│  ├── post-json-with-headers - HTTP POST returning headers       │
│  └── Uses :ttag :http-json for raw Lisp HTTP                    │
├─────────────────────────────────────────────────────────────────┤
│                    mcp-proxy + acl2-mcp                         │
│  mcp-proxy acl2-mcp --transport streamablehttp --port 8000      │
│  ├── Wraps acl2-mcp stdio server as HTTP endpoint               │
│  └── Uses Mcp-Session-Id header for session management          │
└─────────────────────────────────────────────────────────────────┘
```

### MCP Transport Session Protocol

The streamable HTTP transport requires session management:

1. **Initialize**: POST to `/mcp` with `{"method": "initialize", ...}`
2. **Get Session ID**: Response header `Mcp-Session-Id: <uuid>`
3. **Subsequent calls**: Include `Mcp-Session-Id` header in all requests
4. **Tool calls**: POST `{"method": "tools/call", "params": {"name": "evaluate", "arguments": {...}}}`

### Key Files

| File | Purpose |
|------|---------|
| `http-json.lisp` | HTTP POST with JSON, returns response headers |
| `http-json-raw.lsp` | Raw Lisp dexador wrapper |
| `mcp-client.lisp` | MCP JSON-RPC client, session management |
| `mcp-client-raw.lsp` | JSON serialization for MCP protocol |

### Critical Implementation Notes

**1. `include-raw` must come BEFORE functions that call raw Lisp stubs.**

When ACL2 compiles a guard-verified function, it bakes in the calls to other functions. If `include-raw` comes after a function definition, that function will use the **logical stub** (which typically returns nil/error) instead of the raw Lisp implementation.

```lisp
;; WRONG ORDER - mcp-connect will use logical stubs
(defun parse-mcp-session-id (headers) 
  (prog2$ (er hard? ...) nil))  ; Stub
(defun mcp-connect (endpoint state) ...)  ; Compiled with stub
(include-raw "mcp-client-raw.lsp")  ; Too late!

;; CORRECT ORDER - mcp-connect uses raw implementations  
(defun parse-mcp-session-id (headers) 
  (prog2$ (er hard? ...) nil))  ; Stub
(include-raw "mcp-client-raw.lsp")  ; Replaces stub
(defun mcp-connect (endpoint state) ...)  ; Compiled with raw
```

**2. SBCL inlines small functions - must use `(declaim (notinline ...))`**

Even with correct ordering, SBCL may inline tiny stub functions (e.g., ones that just return nil). This causes the compiled function to have the stub code embedded directly, bypassing the symbol-function lookup.

**Solution:** In the raw Lisp file, add `declaim` BEFORE the function definitions:

```lisp
;; In mcp-client-raw.lsp (at the top)
(declaim (notinline parse-mcp-session-id))
(declaim (notinline serialize-mcp-tool-call))
;; ... then define the actual implementations
```

This ensures SBCL always does a runtime function lookup rather than inlining.

### Testing Strategy

**Certification vs Integration Tests are completely separate:**

| Aspect | Certification | Integration Tests |
|--------|---------------|-------------------|
| When | `cert.pl mcp-client.lisp` | Separate script, manual REPL |
| What | Type correctness, guard verification, theorems | Actual HTTP calls to mcp-proxy |
| I/O | None (compile-time only) | Yes (runtime HTTP) |
| MCP server | Not required | Must be running |

**Certification** proves:
- Return types are correct (`mcp-connection-p`, `stringp`, etc.)
- Guards are verified (inputs satisfy preconditions)
- Raw Lisp stubs have correct signatures

**Integration tests** verify:
- HTTP requests actually work
- MCP session protocol is correct
- JSON serialization/parsing works
- Tool calls return expected results

### Integration Test Files

**`test_acl2_mcp_client.py`** — Tests the ACL2 mcp-client.lisp code:

```python
# Run with: python test_acl2_mcp_client.py
# Requires: mcp-proxy running on port 8000, mcp-client.lisp certified

def test_mcp_connect():
    """ACL2 mcp-connect establishes session"""
    
def test_mcp_evaluate():
    """ACL2 mcp-acl2-evaluate: (+ 1 2 3) → 6"""
    
def test_mcp_admit():
    """ACL2 mcp-acl2-admit: defun without saving"""
    
def test_mcp_prove():
    """ACL2 mcp-acl2-prove: simple theorem"""
```

Each test:
1. Starts an ACL2 subprocess
2. Loads mcp-client book
3. Executes MCP client functions
4. Checks output for success patterns

### Running Integration Tests

```bash
# Terminal 1: Start MCP proxy
mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment

# Terminal 2: Run integration tests
cd experiments/agents
python test_acl2_mcp_client.py

# Or test from ACL2 REPL (manual)
(include-book "mcp-client")
(mv-let (err conn state)
  (mcp-connect "http://localhost:8000/mcp" state)
  (if err (cw "Error: ~s0~%" err)
    (b* (((mv e r state) (mcp-acl2-evaluate conn "(+ 1 2)" state)))
      (cw "Result: ~x0~%" r))))
```

---

## MCP Integration (Phase 1.9 - Planned)

After code execution is working, add MCP tool calls for Oxigraph and Qdrant using the same HTTP/JSON-RPC pattern. The ACL2-MCP server can also be integrated for richer ACL2 interaction.

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

1. **Certification** — `cert.pl verified-agent.lisp` or `make experiments/agents/verified-agent.cert`
2. **Interactive testing** — ACL2 MCP server for REPL-driven exploration
3. **Theorem coverage** — Ensure key properties have proofs

### Testing Chat with the Verified Agent

#### Option 1: ACL2-MCP Interactive Session

Start a persistent ACL2 session using ACL2-MCP tools:

```lisp
;; Start session and load the verified agent
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/verified-agent")

;; Create initial agent state
(defconst *test-state*
  (make-agent-state 
    :max-steps 10
    :token-budget 5000
    :time-budget 300
    :file-access 1      ; read access
    :execute-allowed nil
    :max-context-tokens 4000))

;; Initialize conversation
(defconst *state-with-conv*
  (init-agent-conversation 
    "You are a helpful assistant that follows user instructions."
    *test-state*))

;; Check messages
(get-messages *state-with-conv*)
;; => (((:SYSTEM) "You are a helpful assistant..."))

;; Add user message
(defconst *state-with-user*
  (add-user-msg "Hello, what can you help me with?" *state-with-conv*))

;; Simulate assistant response
(defconst *state-with-response*
  (add-assistant-msg "I can help with code analysis and questions!" *state-with-user*))

;; Check conversation preserved must-respond-p
(must-respond-p *state-with-response*)  ; => NIL (can continue)
(should-continue-p *state-with-response*)  ; => T (should continue)

;; Test context truncation
(messages-fit-p (get-messages *state-with-response*) 4000)  ; => T
```

#### Option 2: Full LLM Integration Test

Test with actual LLM (requires LM Studio running on host):

```lisp
;; Load LLM client
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/llm-client")

;; Get available models
(mv-let (err models state)
  (llm-list-models state)
  (mv (if err
          (cw "Error: ~s0~%" err)
        (cw "Models: ~x0~%" models))
      state))

;; Create conversation using FTY constructors
(defconst *messages*
  (list (chat-message (chat-role-system) "You are a helpful assistant.")
        (chat-message (chat-role-user) "What is 2+2?")))

;; Call LLM (requires LM Studio at host.docker.internal:1234)
(mv-let (err response state)
  (llm-chat-completion "google/gemma-3-4b" *messages* state)
  (mv (if err
          (cw "Error: ~s0~%" err)
        (cw "Response: ~s0~%" response))
      state))
```

#### Option 3: Python Test Harness

Create a Python wrapper for end-to-end testing:

```python
# test_verified_agent.py
import subprocess
import json

def test_context_truncation():
    """Test that context management preserves system prompt."""
    # Create long conversation that needs truncation
    messages = [{"role": "system", "content": "System prompt"}]
    for i in range(100):
        messages.append({"role": "user", "content": f"Message {i}" * 100})
        messages.append({"role": "assistant", "content": f"Response {i}" * 100})
    
    # Verify in ACL2 session that truncation preserves system
    # (Implementation: shell out to acl2 or use ACL2-MCP)
    pass

def test_conversation_flow():
    """Test full ReAct conversation flow."""
    pass
```

### Runtime Level

1. **Property-based testing** — Generate random states, verify invariants
2. **Integration tests** — End-to-end with mock MCP tools
3. **Constraint validation** — Compare ACL2 decisions with Z3 decisions

---

## File Structure

```
experiments/agents/
├── verified-agent.lisp      # Main agent implementation (v1.4)
├── verified-agent.acl2      # Certification setup
├── verified-agent.cert      # Generated certificate
├── context-manager.lisp     # Context length management (v1.3)
├── context-manager.cert     # Generated certificate
├── llm-types.lisp           # FTY message types (v1.1)
├── llm-types.cert            
├── llm-client.lisp          # HTTP client wrapper (v1.1)
├── llm-client-raw.lsp       # JSON serialization (v1.1)
├── llm-client.acl2          # Cert setup with ttags (v1.1)
├── http-json.lisp           # HTTP POST utilities
├── Verified_Agent_Spec.md   # This specification
└── (future)
    ├── verified-agent-v2.lisp   # With facts/goals
    ├── mcp-client.lisp          # MCP JSON-RPC client
    └── z3_constraints.py        # Extracted constraints

acl2-mcp/                    # External driver for code execution
├── acl2_mcp/
│   ├── server.py            # MCP server implementation
│   └── ...
└── README.md
```

**Note:** `code-exec.lisp`, `code-exec.acl2`, `code-exec-demo.lisp` have been removed. Code execution is now handled by acl2-mcp as an external driver.

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

### Learnings from Context Manager Implementation

#### 1. FTY Case Macros Require Variables

FTY-generated case macros (`chat-role-case`, `error-kind-case`, etc.) require a variable, not an expression:

```lisp
;; WRONG - causes macro expansion error
(chat-role-case (chat-message->role msg)
  :system ...)

;; CORRECT - bind to variable first
(let ((role (chat-message->role msg)))
  (chat-role-case role
    :system ...))
```

#### 2. ACL2 Binary Minus Only Takes 2 Arguments

```lisp
;; WRONG - ACL2's binary-* minus macro only takes 2 args
(- a b c)

;; CORRECT - nest the calls
(- (- a b) c)
```

#### 3. Explicit Fixes for FTY Return Types

When FTY functions are used in return positions, sometimes you need explicit fix wrappers:

```lisp
(define extract-system-message ((msgs chat-message-list-p))
  :returns (msg (or (chat-message-p msg) (not msg)))
  (b* ((msgs (chat-message-list-fix msgs)))
    (if (and (consp msgs)
             (let ((role (chat-message->role (car msgs))))
               (chat-role-case role :system t :otherwise nil)))
        (chat-message-fix (car msgs))  ; <- explicit fix for return type
      nil)))
```

#### 4. Prove Preservation Lemmas Before Guard Verification

When calling a function with a guard that checks conditions on input, and your input is the result of another function, prove that the intermediate function preserves those conditions:

```lisp
;; add-assistant-msg changes :messages but react-step needs (not (must-respond-p st))
;; Prove this first:
(defthm add-assistant-msg-preserves-must-respond-p
  (equal (must-respond-p (add-assistant-msg content st))
         (must-respond-p st)))

;; Now this function's guards verify:
(define react-step-with-conversation (... (st agent-state-p))
  :guard (not (must-respond-p st))
  (b* ((st (add-assistant-msg msg st))  ; preserves guard condition
       (st (react-step action tool st))) ; guard satisfied
    ...))
```

#### 5. Use `nfix` and `truncate` Instead of `ceiling`

ACL2's `ceiling` can cause proof difficulties with natural number bounds. Use `truncate` with adjustment:

```lisp
;; Conservative ceiling division: chars/4 rounded up
(define estimate-tokens ((chars natp))
  :returns (tokens natp)
  (nfix (truncate (+ chars 3) 4)))  ; (n+3)/4 = ceiling(n/4) for n≥0
```

---

## References

- [ACL2 FTY Documentation](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=FTY____FTY)
- [Oxigraph](https://github.com/oxigraph/oxigraph) — RDF graph database
- [Horned-OWL](https://github.com/phillord/horned-owl) — OWL library
- [Qdrant](https://github.com/qdrant/qdrant) — Vector similarity search
- [LangGraph](https://github.com/langchain-ai/langgraph) — Agent orchestration

---

## Changelog

### v1.5 (2025-12-31)
- **Code Execution via External Driver (Phase 1.8)** — Simplified architecture
  - acl2-mcp serves as external driver for code execution
  - Removed `code-exec.lisp`, `code-exec.acl2`, `code-exec-demo.lisp`
  - ACL2s interface books are for CL→ACL2 calls, not ACL2 books
  - Verified core remains simple: just permission checks
  - Error messages tested and confirmed useful for LLM learning
  - External driver handles: markdown extraction, acl2-mcp calls, result formatting
- **Key insight:** Keep verified ACL2 code simple and inspectable; push complexity to external drivers
- Updated copilot-instructions.md to reference this spec

### v1.4 (2025-12-31)
- **Code Execution (Phase 1.8)** — ACL2 code execution via `acl2s-compute`
  - Simplified implementation using ACL2s interface books directly
  - Deleted `code-exec-raw.lsp` (unnecessary custom wrappers)
  - Rewrote `code-exec.lisp` to use `acl2s-interface::acl2s-compute`
  - Extract code from both ` ```acl2` and ` ```lisp` markdown blocks
  - Error messages captured and returned to LLM for learning
  - Integrates with verified agent's `execute-allowed` permission
  - Tool specification: `*acl2-compute-tool*` with `:requires-execute t`
- **Key insight:** ACL2s books provide complete plumbing—no custom raw Lisp needed
- Updated MCP Integration to Phase 1.9 (after code execution)

### v1.3 (2025-12-30)
- **Context Management (Phase 1.6)** — Verified conversation history with context length management
  - New `context-manager.lisp` book with sliding window truncation
  - Token estimation (4 chars/token conservative)
  - System prompt always preserved (`truncate-preserves-system-prompt` theorem)
  - Output truncation following mini-swe-agent pattern (head+tail)
  - Extended `agent-state` with `messages`, `max-context-tokens`, `system-prompt`
  - New conversation functions: `init-agent-conversation`, `add-user-msg`, `add-assistant-msg`, `add-tool-result`
  - `react-step-with-conversation` for integrated ReAct + conversation management
  - Conversation preservation theorems (adding messages doesn't affect control flow)
- Updated architecture diagram with context management layer
- Added comprehensive testing instructions for chat interaction
- **Learnings documented:**
  - FTY case macros require variables, not expressions (use `let` binding)
  - ACL2's binary `-` only takes 2 args (nest for 3+)
  - Need explicit `chat-message-list-fix` wrappers for return types
  - Prove preservation lemmas before using functions in guards

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
