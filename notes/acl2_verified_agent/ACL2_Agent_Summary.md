# ACL2 Verified Agent Design: Executive Summary

## The Approach

**Goal**: Build a trustworthy foundational agent that can generate verified code for other agents.

**Strategy**: 
1. All reasoning/decision-making happens in ACL2 (proven correct)
2. External tools (LLMs, MCP servers) are unverified oracles
3. We prove agent behavior is correct GIVEN ANY responses from those oracles
4. HTTP/JSON marshaling is unverified but sandboxed

**Result**: A verified control system that safely orchestrates unverified services.

---

## Why This Architecture?

### The Fundamental Insight

ACL2's **pure functional paradigm** makes the agent's reasoning trivially verifiable:
- Reasoning = pure function: `(think facts goals) → decision`
- Decisions are deterministic (same input = same output)
- Proofs are straightforward induction over reasoning steps
- No concurrency, no undefined behavior, no side effects

The only unverified part is **external tool calls** - but those are isolated:
- Agent specifies formal preconditions
- Tool responses are parsed into formal facts
- Agent behavior proven regardless of tool correctness

### Why STObj?

**STObj** = efficiently mutable state that's logically immutable
- Agent state modified via `(update-field value stobj)`
- In execution: O(1) destructive update in Common Lisp
- In logic: Treated as functional (no aliasing)
- Result: Can prove properties about stateful agent

### Why ReAct/CoT?

**ReAct** (Reasoning + Acting) is perfect for verified agents:
- Think → Select → Verify → Call → Observe → Loop
- Each step is a pure function
- Each step is independently verifiable
- Chain of functions is composable proofs

---

## Key Design Decisions

### 1. Verified vs Unverified Components

**In ACL2** ✓ **Verified**:
- `think(state, goals) → next-goal` - Pure reasoning
- `select-action(goal, facts) → action` - Deterministic selection
- `verify-preconditions(action, state)` - Safety checks
- State machine transitions
- Resource bounds (max steps, max facts)

**Outside ACL2** ✗ **Unverified** (but safe):
- LLM API calls - treated as oracle
- JSON parsing - validated with bounds
- HTTP transport - trusted infrastructure
- MCP server responses - validated before use

### 2. State Representation (STObj)

```
Agent State:
├─ facts: Array of known facts (knowledge base)
├─ beliefs: Confidence scores for facts
├─ goals: Stack of goals being pursued
├─ history: Audit trail of reasoning
├─ step-counter: Resource tracking
└─ error-state: Safety flag
```

All operations on state are:
- Single-threaded (no concurrency issues)
- Deterministic (same input → same output)
- Bounded (resource constraints proven)

### 3. External Tool Interface

```lisp
; Define tool contract abstractly
(encapsulate ((external-tool (query facts) t))
  
  ; Assumptions about responses
  (defthm tool-always-returns-list
    (true-listp (external-tool query facts)))
  
  (defthm tool-bounded
    (< (length (external-tool query facts)) 10000)))

; Prove agent correct FOR ANY tool implementation
(defthm agent-safe-regardless-of-tool
  (implies (valid-initial-state state)
           (agent-terminates-safely (run-agent state))))
```

Key: **Agent correctness doesn't depend on which LLM or tool is used.**

---

## Development Roadmap

### Phase 1: Foundation (Steps 1-2)
- Learn ACL2 basics (functions, induction, simple proofs)
- Implement minimal agent state with STObj
- Write first theorems about state operations
- **Goal**: Understand how ACL2 works

### Phase 2: ReAct Loop (Steps 3-4)
- Implement reasoning functions (pure logic)
- Build tool selection logic
- Add precondition verification
- Prove main loop terminates
- **Goal**: Working ReAct cycle with basic theorems

### Phase 3: External Integration (Steps 5-6)
- Define abstract tool contracts
- Implement JSON/HTTP bridge (unverified)
- Prove agent handles responses safely
- Add resource bounds
- **Goal**: Agent can call real LLM/tools safely

### Phase 4: Verification Theorems (Steps 7-8)
- Prove agent is sound (decisions respect policies)
- Prove agent is safe (never enters error state)
- Prove agent makes progress (toward goals or bounded)
- Prove agent is deterministic
- **Goal**: Formal guarantees about agent behavior

### Phase 5: Multi-Agent & Semantics (Steps 9-10)
- Prove agents compose safely
- Integrate with wiki3.ai semantic web
- RDF assertions formally verified
- **Goal**: Verified knowledge graph integration

---

## Essential ACL2 Features

### 1. **STObj** - Single-Threaded State Container
```lisp
(defstobj ag
  (facts :type (array t (1000)))
  (num-facts :type (integer 0 *))
  (goals :type (array t (100)))
  (steps :type (integer 0 *)))
```
**Why**: Efficient mutable state that's logically immutable for proofs.

### 2. **Pure Functions** - Reasoning Logic
```lisp
(defun think (facts goals)
  (cond ((goal-achieved goals facts) 'success)
        (t (select-next-goal goals))))
```
**Why**: No side effects make proofs trivial.

### 3. **Defthm** - Proving Properties
```lisp
(defthm agent-terminates
  (implies (< steps max-steps)
           (terminates-p (run-agent state steps))))
```
**Why**: Formal guarantees about behavior.

### 4. **MBE** - Logic vs Execution
```lisp
(defun json-parse (s)
  (mbe :logic (slow-safe-parser s)
       :exec (fast-parser s)))
```
**Why**: Prove specification, execute efficiently.

### 5. **Encapsulation** - Abstract Specs
```lisp
(encapsulate ((external-tool (query) t))
  (defthm tool-bounded ...))
```
**Why**: Prove agent correctness for ANY tool implementation.

---

## Books to Study (Reading Order)

1. **Computer-Aided Reasoning: An Approach** (Kaufmann, Manolios, Moore)
   - Chapters 2-7 (Functional programming, state, proofs)

2. **ACL2 Manual** (Online)
   - Focus: `:doc defstobj`, `:doc defthm`, `:doc induction`

3. **Case Studies** (Kaufmann et al.)
   - Chapter 8 (Microprocessor = complex state machine)
   - Chapter 9 (Embedded Verifier = agent-like system)

4. **Russinoff "Floating-Point Hardware Verification"**
   - "High-Speed Executable Models" chapter
   - Shows proving + performance together

---

## Key Theorems to Prove

### Soundness
```lisp
(defthm decisions-respect-preconditions
  "If agent decides action, preconditions hold"
  (implies (and (select-action action)
                (agent-state-valid state))
           (preconditions-met action state)))
```

### Safety
```lisp
(defthm agent-never-crashes
  "Agent handles all responses gracefully"
  (implies (valid-initial-state s)
           (no-error-state (run-agent s))))
```

### Termination
```lisp
(defthm agent-terminates
  "Agent always finishes within step limit"
  (implies (natp max-steps)
           (terminates-in-steps (run-agent s) max-steps)))
```

### Determinism
```lisp
(defthm reasoning-deterministic
  "Same state → same decision"
  (implies (equal state1 state2)
           (equal (think state1) (think state2))))
```

---

## What Makes This Different

### Traditional Agents
- Unverified reasoning
- Black-box LLM calls
- No guarantees on behavior
- Ad-hoc error handling

### wiki3.ai Verified Agent
- ✅ Reasoning proven correct
- ✅ Tool calls sandboxed + verified
- ✅ Formal guarantees on:
  - Termination
  - Safety
  - Resource bounds
  - Determinism
- ✅ Can generate verified code for other agents

---

## Why ACL2 (Not Z3)?

**For initial ReAct agent**:
- Pure functional reasoning = ACL2's sweet spot
- Inductive proofs are natural
- STObj for state management is perfect
- No need for SMT solver yet

**Later, for code reasoning**:
- Add SMTLink for Z3 when code logic requires it
- But core agent loop stays in ACL2

---

## Success Criteria

### Step 2 ✓
- [ ] Understand ACL2 basics
- [ ] STObj defined and working
- [ ] First 3 simple theorems proven

### Step 4 ✓
- [ ] Full ReAct loop implemented
- [ ] Loop provably terminates
- [ ] 10+ theorems about behavior

### Step 6 ✓
- [ ] External tool interface working
- [ ] Safe HTTP/JSON bridge
- [ ] Agent calls real LLM

### Step 8 ✓
- [ ] Major soundness theorem proven
- [ ] Resource bounds proven
- [ ] Determinism proven
- [ ] Ready for multi-agent integration

---

## Next Immediate Actions

### Today
1. Review this document (understand architecture)
2. Install ACL2 from cs.utexas.edu/~moore/acl2/
3. Run `(acl2)` and verify it works

### This Step
1. Read "Computer-Aided Reasoning" Chapter 2 (Lisp basics)
2. Study `:doc defstobj` in ACL2 manual
3. Write `agent-state.lisp` (STObj definition)
4. Prove 1-2 simple theorems about adding facts

### Next Step
1. Complete Chapter 3-4 of CAR book
2. Implement `reasoning.lisp` (pure logic functions)
3. Implement `react-loop.lisp` (main cycle)
4. Prove ReAct loop terminates

### Step 3-4
1. External tool interface (contract + oracle)
2. Resource bound theorems
3. Soundness theorem
4. Test with real LLM call

---

## Resources

**Books**:
- CS: www.cs.utexas.edu/~moore/publications/acl2-books/
- Free PDFs available

**Documentation**:
- ACL2 Manual: www.cs.utexas.edu/~moore/acl2/v8-6/combined-manual/
- Searchable, comprehensive

**Community**:
- ACL2 Workshop (annual)
- Mailing list: acl2@utexas.edu
- GitHub: acl2/acl2

**For wiki3.ai integration**:
- Kestrel Institute (formal methods)
- Contact for ACL2 expert support

---

## The Big Picture

You're building a **verified control system** that:

1. **Reasons provably correctly** (ACL2 proves it)
2. **Calls unverified oracles safely** (LLMs, tools)
3. **Makes guaranteed decisions** (no hallucinations in control flow)
4. **Can generate verified code** (for other agents)
5. **Integrates with semantic web** (RDF + verification)

This is **production-grade formal methods** applied to AI agents.

The agent itself is verified. The LLM it calls is not. But the **combination is trustworthy** because the agent's logic is proven.

---

## Questions to Discuss

1. Should agent learn/adapt rules, or stick to fixed logic?
2. How much reasoning in ACL2 vs delegated to LLM?
3. What level of theorem proving required before MVP?
4. How to handle partial information/uncertainty formally?
5. Integration timeline with wiki3.ai platform?

---

**You now have everything you need to start building.**

The path is clear: 8 steps to a verified agent foundation.

Let's build something trustworthy.
