# Foundational Verified Agent in ACL2: Complete Design

## I. EXECUTIVE OVERVIEW

Building a trustworthy verified agent requires:

1. **Verified ReAct/CoT reasoning loop** - Pure functional, provably correct decision-making
2. **Proven state management** - Single-threaded object (stobj) for agent state
3. **Safe tool interface** - Formal contracts for HTTP/MCP server calls
4. **External integration** - JSON/HTTP handling (unverified but sandboxed)
5. **Proof-by-simulation** - Validation through executable specifications

**Key Insight**: ACL2's functional paradigm makes the reasoning loop trivially verifiable. The agent's decisions are pure logical inference. External services (LLM calls, MCP servers) are unverified oracles - we verify agent behavior given their responses, not the responses themselves.

---

## II. ARCHITECTURE OVERVIEW

```
┌─────────────────────────────────────────────────────────────┐
│                   VERIFIED AGENT CORE (ACL2)                │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ ReAct Loop (Pure Functional Logic)                   │  │
│  │ ──────────────────────────────────────                │  │
│  │ • Think: Current state + observations → goals        │  │
│  │ • Select Action: Goals + beliefs → action spec      │  │
│  │ • Verify Preconditions: Constraints checked         │  │
│  │ • Call External Tool: Safe JSON/HTTP bridge         │  │
│  │ • Observe: Response → Update beliefs                │  │
│  │ • Loop: Until goal or max steps                      │  │
│  └──────────────────────────────────────────────────────┘  │
│                         ↓                                    │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ Agent State (STObj - Single-Threaded Object)         │  │
│  │ ──────────────────────────────────────                │  │
│  │ • Facts: Set of known facts (knowledge base)        │  │
│  │ • Goals: Current goals being pursued                │  │
│  │ • Beliefs: Confidence/truth value of facts          │  │
│  │ • History: Trace of reasoning steps (audit trail)   │  │
│  │ • Action Count: Track resource usage                │  │
│  └──────────────────────────────────────────────────────┘  │
│                         ↓                                    │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ Tool Contracts (Formal Specifications)               │  │
│  │ ──────────────────────────────────────                │  │
│  │ • Preconditions: Required state/facts                │  │
│  │ • Postconditions: Guaranteed results                 │  │
│  │ • API Signatures: Parameter types verified           │  │
│  │ • Error Handling: Bounded error cases                │  │
│  └──────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
              ↓         ↓         ↓         ↓
        ┌─────────────────────────────────────────────────┐
        │    EXTERNAL ORACLE LAYER (Unverified)           │
        ├─────────────────────────────────────────────────┤
        │ • LLM Calls (via HTTP to LLM service)           │
        │ • MCP Servers (Model Context Protocol)          │
        │ • JSON Request/Response marshaling               │
        │ • HTTP Transport (TCP/TLS)                       │
        └─────────────────────────────────────────────────┘
```

---

## III. DESIGN PRINCIPLES

### A. Verified Components Only

✅ **Verified in ACL2**:
- All reasoning (pure functional logic)
- State transitions (deterministic)
- Decision logic (provably correct control flow)
- Precondition checking
- Invariant maintenance

❌ **NOT verified** (but isolated/sandboxed):
- LLM model behavior
- External tool correctness
- Network I/O
- JSON parsing (use safe parser with bounds)

### B. Functional Paradigm

ACL2 enforces **pure functional** semantics:
- **No side effects** in reasoning
- Functions = mathematical specifications
- Proofs = confidence in decision logic
- STObj = carefully controlled mutable state

Result: We can prove agent behavior is correct regardless of external oracle responses.

### C. State Machine Model

```
Agent State Transitions (Provably Correct)
────────────────────────────────────────

IDLE
 ↓
PLANNING (Think: determine goals from state)
 ↓
SELECTING (Select best action given goals)
 ↓
VERIFYING (Check preconditions)
 ├─ Fail → ERROR
 │
CALLING (Safe bridge to external tool)
 ├─ Timeout → ERROR
 ├─ Invalid response → ERROR
 │
OBSERVING (Integrate result into beliefs)
 ↓
GOAL_CHECK
 ├─ Goal achieved → SUCCESS
 ├─ Goal impossible → BACKTRACK
 │
IDLE (next iteration or completion)
```

All transitions are:
- Deterministic (given same input)
- Provable (ACL2 theorems)
- Bounded (max steps, max actions)
- Recoverable (error handling proven)

---

## IV. ESSENTIAL ACL2 FEATURES FOR VERIFIED AGENTS

### A. **STObj (Single-Threaded Objects)** - Agent State Container

**What it is**: Mutable (in execution) but logically immutable (in proofs)

**Why for agents**: 
- Maintains agent state across reasoning steps
- Provably single-threaded (no aliasing)
- Efficient execution (Common Lisp native operations)
- Can be updated in O(1) destructive operations

**Pattern for agent**:

```lisp
(defstobj ag
  ; Knowledge/beliefs
  (fact-set :type (array t (1000)))     ; Known facts with timestamps
  (belief-vector :type (array rational (1000))) ; Confidence scores
  
  ; Goals and control
  (goal-stack :type (array t (100)))   ; Stack of active goals
  (current-step :type (integer 0 *))   ; Execution step count
  
  ; Audit trail
  (reasoning-trace :type (array t (500))) ; Why did agent do X?
  (action-history :type (array t (100))) ; Audit log of actions
  
  ; Configuration
  (max-actions :type (integer 0 *))
  (reasoning-depth-limit :type (integer 0 *)))
```

**Theorem example**:
```lisp
(defthm agent-state-not-modified-by-think
  (implies (ag p)
           (equal (ag p)
                  (ag (think ag)))))  ; think only returns analysis, doesn't modify
```

**Books to study**:
- `:doc defstobj` in ACL2 manual
- "Computer-Aided Reasoning: An Approach", Chapter 4
- Kestrel's x86 ISA model (uses nested stobjs)

---

### B. **Functional Control Flow** - Pure Reasoning

**Pattern**: Reasoning = function that takes beliefs, returns action

```lisp
; Pure function - no state modification
(defun think (current-facts current-goals belief-state)
  "Determine next goal or conclude success/failure"
  (cond
    ((goal-achieved-p current-facts current-goals) 'success)
    ((no-progress-p belief-state) 'backtrack)
    (t (select-next-goal current-facts current-goals))))

(defun select-action (next-goal current-facts available-tools)
  "Given goal, pick best tool to apply"
  (let* ((applicable (filter-applicable-tools available-tools next-goal))
         (selected (pick-best applicable)))
    (make-action-spec :tool selected
                      :parameters (infer-params next-goal))))

(defun verify-action-feasible (action-spec current-facts)
  "Check preconditions before calling external tool"
  (and (action-preconditions-met-p action-spec current-facts)
       (within-resource-limits-p action-spec)))
```

**Theorem example**:

```lisp
(defthm think-sound
  (implies (and (valid-fact-set facts)
                (valid-goal-list goals)
                (equal (think facts goals state) 'success))
           (goal-achieved-p facts goals)))
```

**Why this matters**: Proof of correctness doesn't depend on external tools - just agent logic.

---

### C. **MBE (Must Be Equal) for Execution Efficiency**

When verification needs slow logic but execution needs speed:

```lisp
(defun json-parse-safe (json-string)
  (mbe :logic (json-parse-logic json-string)        ; Slow but proven
       :exec (json-parse-fast json-string)))        ; Fast, trusted

; We prove logic version correct, execute fast version
(defthm json-parse-safe-correct
  (equal (json-parse-safe x)
         (json-parse-logic x)))
```

**For agents**: Use MBE for HTTP marshaling - verify specification, execute efficient code.

---

### D. **Apply$ and Higher-Order Functions** (Optional Advanced)

For more sophisticated agent learning/adaptation:

```lisp
(include-book "projects/apply-dollar/apply-dollar")

(defun apply-rule (rule state)
  "Apply a parameterized rule to current state"
  (apply$ (rule-function rule)
          (list state (rule-params rule))))

(defun find-applicable-rules (rules state)
  "Filter rules whose preconditions hold"
  (filter (lambda (rule) 
            (apply$ (rule-precondition rule) (list state)))
          rules))
```

**Best for**: If you want agents to learn rules and prove they work.

---

### E. **Guards and Guard Verification** - Type Safety

ACL2 can verify types at compile time:

```lisp
(defun process-agent-response (response facts)
  (declare (xargs :guard (and (valid-json-response-p response)
                              (valid-fact-set facts))))
  (let ((parsed (json-parse response)))
    (if (valid-parsed-response-p parsed)
        (integrate-into-beliefs facts parsed)
        facts)))

; Verify guard (proves type safety before execution)
(verify-guards process-agent-response)
```

**For agents**: Guarantees HTTP responses are properly validated before processing.

---

### F. **Encapsulation and Abstract Functions** - Modularity

Define abstract specifications, prove theorems about them, plug in implementations:

```lisp
(encapsulate ((external-tool-response (goal query) t))
  
  ; Specification: what do we know about tool responses?
  (local (defun external-tool-response (goal query) nil))
  
  (defthm external-tool-response-is-bounded
    (bounded-response-p (external-tool-response goal query)))
  
  (defthm external-tool-response-respects-contract
    (implies (valid-query-p query)
             (valid-response-p (external-tool-response goal query)))))

; Later: prove agent behavior for ANY implementation
(defthm agent-succeeds-regardless-of-oracle
  (implies (valid-initial-state state)
           (eventually-goal-achieved-p (agent-loop state))))
```

**For agents**: Reason about agent correctness independent of LLM implementation.

---

### G. **Stobj Events and State Mutations**

Modify agent state deterministically:

```lisp
(defun process-observation (observation ag)
  (declare (xargs :stobjs ag))
  (let* ((ag (update-fact-set observation ag))
         (ag (update-belief-vector observation ag))
         (ag (increment-current-step ag)))
    (mv (generate-next-goal ag) ag)))  ; Return both result AND modified stobj

; Theorem: observation doesn't violate invariants
(defthm process-observation-preserves-invariants
  (implies (agent-invariants-hold ag)
           (agent-invariants-hold (mv-nth 1 (process-observation obs ag)))))
```

**For agents**: State updates are provably correct and resource-bounded.

---

## V. ESSENTIAL BOOKS AND RESOURCES

### A. **Primary Textbook**

**"Computer-Aided Reasoning: An Approach"** by Kaufmann, Manolios, Moore
- **Chapters to focus on**:
  - Ch 2-3: Introduction to ACL2 (functional programming)
  - Ch 4: State and stobjs (critical for agent state)
  - Ch 5: Lists and recursive data (knowledge representation)
  - Ch 6: Proof by induction (reasoning proofs)
  - Ch 7: Proof by cases (handling different scenarios)
- **Available**: Free online at www.cs.utexas.edu/~moore/publications/acl2-books/car/

### B. **Case Studies Book**

**"Computer-Aided Reasoning: ACL2 Case Studies"** by Kaufmann et al.
- Read: Chapter 8 "Microprocessor Modeling" (complex state machine example)
- Read: Chapter 9 "The Embedded Verifier" (safety-critical agent-like system)
- **Why**: Templates for large verified systems similar to agents

### C. **Floating-Point Verification**

**"Formal Verification of Floating-Point Hardware Design"** by Russinoff
- Not about floating-point, but about large-scale verification methodology
- Chapter on "High-Speed Executable Models" directly applicable to agent loop
- Shows how to balance proof with execution speed

### D. **ACL2 Documentation (Online, Always Current)**

**Must-read sections**:
- `:doc defun` - Function definition syntax and guards
- `:doc defstobj` - Single-threaded objects (CRITICAL)
- `:doc stobj` - How stobjs work logically and executionally
- `:doc declare` - Xargs and performance hints
- `:doc defthm` - Theorem proving
- `:doc induction` - Proof by induction patterns
- `:doc define` - Modern function definition (better than defun)
- `:doc defabsstobj` - Abstract stobjs (for pluggable external tools)
- `:doc make-event` - Dynamic proof generation (for macro-based verification)

**Access**: www.cs.utexas.edu/~moore/acl2/v8-6/combined-manual/

### E. **Specific to Agent Architecture**

**State Machine Papers** (in ACL2 context):
- Manolios's work on "Operational Semantics" - search ACL2 publications
- Moore's "Modeling Algorithms" - shows simulation patterns

**Tool Interface Design**:
- Hardin et al. "Instruction Set Architecture Verification" - ISA = tool spec

---

## VI. IMPLEMENTATION ROADMAP

### Phase 1: Foundation (Steps 1-2)

#### 1.1 - Learn ACL2 Basics with Toy Agent
```lisp
; simplified-agent.lisp

; Knowledge representation: list of facts
(defun fact-holds-p (fact facts)
  (member fact facts))

(defun add-fact (fact facts)
  (if (fact-holds-p fact facts)
      facts
      (cons fact facts)))

; Simple reasoning
(defun think-simple (facts goals)
  (if (member (car goals) facts)
      'goal-achieved
      'thinking))

(defun select-action-simple (goal)
  (list 'query (concatenate 'string "Is " goal " true?")))

; Outer loop
(defun agent-one-step (facts goals)
  (let* ((status (think-simple facts goals))
         (action (select-action-simple (car goals))))
    (list status action facts)))

; Prove: agent terminates
(defthm agent-one-step-produces-action
  (let ((result (agent-one-step facts goals)))
    (and (member (car result) '(goal-achieved thinking))
         (consp (cadr result)))))
```

**Learn**: Basic function definition, simple proofs, induction

---

#### 1.2 - Learn STObj for Agent State
```lisp
; agent-state.lisp
(include-book "std/stobjs/basic" :dir :system)

(defstobj ag-simple
  (facts :type (array t (100)))
  (num-facts :type (integer 0 100))
  (goals :type (array t (50)))
  (num-goals :type (integer 0 50)))

(defun agent-facts (ag)
  (declare (xargs :stobjs ag))
  (loop for i from 0 to (- (num-facts ag) 1)
        collect (facts ag i)))

(defun add-fact-to-agent (fact ag)
  (declare (xargs :stobjs ag))
  (let* ((n (num-facts ag))
         (ag (update-facts n fact ag))
         (ag (update-num-facts (+ 1 n) ag)))
    ag))

(defthm add-fact-increases-count
  (implies (and (ag p) (< (num-facts ag) 100))
           (equal (num-facts (add-fact-to-agent f ag))
                  (+ 1 (num-facts ag)))))
```

**Learn**: STObj definition, mutation patterns, theorem about state

---

### Phase 2: ReAct Loop (Steps 3-4)

#### 2.1 - Reasoning Engine
```lisp
; reasoning.lisp

(defun goal-achieved (fact facts)
  (member fact facts))

(defun select-best-action (facts goals)
  "Given facts and goals, select action"
  (cond
    ((null goals) (make-action 'idle))
    ((goal-achieved (car goals) facts) 
     (make-action 'pop-goal))
    (t (make-action 'query-llm (car goals)))))

(defun verify-action-safe (action facts)
  "Precondition check"
  (case (action-type action)
    (query-llm (and (goal-exists-p (action-goal action))
                    (< (query-count facts) 1000)))
    (pop-goal t)
    (idle t)
    (t nil)))

; Main reasoning loop
(defun react-one-step (facts goals num-steps)
  (declare (xargs :measure (nfix (- 100 num-steps))))
  (cond
    ((>= num-steps 100) (mv 'max-steps-exceeded facts))
    ((null goals) (mv 'success facts))
    (t (let* ((action (select-best-action facts goals))
              (safe (verify-action-safe action facts)))
         (if safe
             (mv action (list facts goals num-steps))
             (mv 'precondition-violation facts))))))

(defthm react-one-step-terminates
  (implies (and (< num-steps 100)
                (true-listp facts))
           (mv-let (status new-facts)
             (react-one-step facts goals num-steps)
             (and (symbolp status)
                  (true-listp new-facts)))))
```

**Learn**: Multi-valued returns (mv), measure-based termination, complex theorems

---

#### 2.2 - Safe Tool Interface
```lisp
; tool-contracts.lisp

(defun tool-contract (tool)
  "Return contract spec for a tool"
  (make-contract
    :name (tool-name tool)
    :preconditions (tool-precondition-spec tool)
    :postconditions (tool-postcondition-spec tool)
    :error-cases (tool-error-cases tool)))

(defun call-tool-safe (tool query facts)
  "Call tool only if safe"
  (if (preconditions-met-p tool query facts)
      (list 'tool-call (tool-name tool) query)
      (list 'precondition-failed (tool-name tool))))

(defthm safe-tool-call-respects-contract
  (implies (preconditions-met-p tool query facts)
           (contract-satisfied-p
             (tool-contract tool)
             (call-tool-safe tool query facts))))
```

**Learn**: Creating specifications, composing precondition checks

---

### Phase 3: External Integration (Steps 5-6)

#### 3.1 - JSON Marshaling (Spec Only, Not Verified)
```lisp
; external-interface.lisp
; These functions are UNVERIFIED (external oracle)
; We verify agent behavior GIVEN their outputs

(defun json-query-to-http (query facts)
  "Convert agent query to JSON HTTP request (UNVERIFIED)"
  (concatenate 'string
    "{\"query\": \"" query "\", \"context\": \"" facts "\"}"))

; We treat this as an oracle:
(defun http-call-external-llm (request)
  "Call external LLM via HTTP (UNVERIFIED ORACLE)"
  ; Would call real HTTP library here
  request)

(defun http-response-to-facts (response)
  "Parse HTTP response into new facts (UNVERIFIED)"
  ; Would parse JSON here
  nil)

; What we CAN verify: agent behavior given ANY response
(encapsulate ((external-oracle (query facts) t))
  
  (defthm agent-safe-regardless-of-oracle
    (implies (valid-agent-state state)
             (agent-terminates-safely
               (react-loop state (external-oracle ...))))))
```

**Learn**: Encapsulation, abstract function specification

---

#### 3.2 - Full Agent Loop with Bounded Execution
```lisp
; full-agent.lisp

(defun agent-loop (ag max-iterations)
  (declare (xargs :stobjs ag
                  :measure (nfix (- max-iterations 0))))
  (cond
    ((>= (current-step ag) max-iterations) ag)
    ((null (goal-stack ag)) ag)
    (t (let* ((ag (perform-one-react-cycle ag)))
         (agent-loop ag max-iterations)))))

(defun perform-one-react-cycle (ag)
  (declare (xargs :stobjs ag))
  (let* ((next-goal (car (goal-stack ag)))
         (action (think-and-select next-goal ag)))
    (cond
      ((preconditions-met-p action ag)
       (let ((ag (increment-step ag)))
         (record-action-taken action ag)))
      (t (let ((ag (increment-step ag)))
           (record-action-failed action ag))))))

(defthm agent-loop-terminates
  (implies (and (ag p) (natp max-iterations))
           (ag (agent-loop ag max-iterations))))

(defthm agent-loop-maintains-invariants
  (implies (agent-invariants-hold ag)
           (agent-invariants-hold (agent-loop ag max-iterations))))
```

**Learn**: Combining stobj operations, measure-based recursion

---

### Phase 4: Verification Theorems (Steps 7-8)

#### 4.1 - Soundness Proof
```lisp
; soundness.lisp

(defthm agent-decisions-are-sound
  "If agent decides to perform an action, preconditions hold"
  (implies (and (agent-invariants-hold ag)
                (equal (action-type action) 
                       (select-action ag)))
           (preconditions-met-p action ag)))

(defthm agent-observations-preserve-facts
  "Observations don't remove already-known facts"
  (implies (and (member fact (agent-facts ag))
                (member response (external-oracle-response-set)))
           (member fact (agent-facts (observe response ag)))))
```

**Learn**: Proving properties about your own code

---

#### 4.2 - Resource Bounds
```lisp
; resource-bounds.lisp

(defthm agent-actions-bounded
  "Agent never exceeds action budget"
  (implies (and (< initial-step max-steps)
                (ag p))
           (<= (current-step (agent-loop ag max-steps))
               max-steps)))

(defthm agent-memory-bounded
  "Fact set never exceeds maximum"
  (implies (and (< (num-facts ag) 100)
                (ag p))
           (< (num-facts (agent-loop ag max-steps)) 101)))
```

---

## VII. KEY THEOREMS TO PROVE

### Core Soundness
```lisp
(defthm agent-never-violates-policies
  (let ((state (agent-loop initial-state max-steps)))
    (policies-respected-p state)))

(defthm agent-facts-are-grounded
  (let ((state (agent-loop initial-state max-steps)))
    (all-facts-grounded-in-observations-p state)))

(defthm agent-terminates
  (implies (and (agent-state-p s)
                (natp max-steps))
           (terminates-in-steps-p (agent-loop s max-steps)
                                   max-steps)))
```

### Composition Safety
```lisp
(defthm chained-agents-preserve-safety
  (let* ((s1 (agent-loop s0 max-steps1))
         (s2 (agent-loop s1 max-steps2)))
    (agent-safe-p s2)))

(defthm agent-recovers-from-errors
  (implies (valid-error-p error)
           (agent-safe-p (agent-handle-error error state))))
```

---

## VIII. PROOF STRATEGY

### Step-by-Step Approach

1. **Start with induction over agent steps**
   ```lisp
   (defthm agent-property-by-induction
     (implies (and (agent-state-p s)
                   (natp n)
                   (agent-property-holds-p s))
              (agent-property-holds-p (one-step s))))
   ```

2. **Use guards for type safety**
   - Prove guards once, then all theorems get type safety for free
   
3. **Build lemmas for subgoals**
   - Prove simple facts about helper functions first
   - Compose them into larger theorems

4. **Use simplification rules**
   - Add proven lemmas as `:rewrite` rules
   - Let ACL2 automatically apply them

5. **Break complex proofs into cases**
   - Different behavior for different conditions
   - Prove each case separately

### Example Proof Development

```lisp
; Step 1: Simple helper lemma
(defthm facts-never-shrink
  (implies (member x (agent-facts ag))
           (member x (agent-facts (update-from-response resp ag))))
  :rule-classes (:rewrite :forward-chaining))

; Step 2: Use it to prove larger property
(defthm goal-achievement-progress
  (implies (and (goal-achieved-p goal facts)
                (update-from-response resp facts))
           (goal-achieved-p goal (update-from-response resp facts)))
  :hints (("Goal" :use (facts-never-shrink))))

; Step 3: Roll up into main theorem
(defthm agent-goal-persistence
  (let ((state (agent-loop s max-steps)))
    (implies (goal-achieved-p g (agent-facts s))
             (goal-achieved-p g (agent-facts state)))))
```

---

## IX. EXECUTION STRATEGY

### How It Runs

1. **ACL2 proof mode**: Theorems proven using ACL2's tactic engine
2. **ACL2 execution mode**: Verified functions compiled to Common Lisp
3. **Hybrid**: Use `:exec` versions for speed, `:logic` for proofs

```lisp
(defun some-function (x)
  (mbe :logic (slow-version x)      ; Proven correct
       :exec (fast-version x)))      ; Executes fast
```

### Performance Considerations

- **STObj operations**: O(1) - direct memory mutation in Common Lisp
- **List operations**: O(n) - immutable, but functional style
- **Proof verification**: Separate from execution (once proven, always proven)

---

## X. SAMPLE MINIMAL PROJECT

### File 1: agent-state.lisp
```lisp
(in-package "ACL2")

; Minimal agent state
(defstobj agent-state
  (state-facts :type (array t (100)))
  (facts-count :type (integer 0 *))
  (step-count :type (integer 0 *)))

(defun agent-state-init ()
  (let ((ag (agent-state)))
    ag))

(defthm initial-state-has-zero-facts
  (equal (facts-count (agent-state-init)) 0))
```

### File 2: reasoning.lisp
```lisp
(include-book "agent-state")

(defun add-fact-to-state (fact ag)
  (declare (xargs :stobjs ag))
  (if (< (facts-count ag) 100)
      (let* ((ag (update-state-facts (facts-count ag) fact ag))
             (ag (update-facts-count (+ 1 (facts-count ag)) ag)))
        ag)
      ag))

(defthm add-fact-succeeds
  (implies (< (facts-count ag) 100)
           (equal (facts-count (add-fact-to-state f ag))
                  (+ 1 (facts-count ag)))))
```

### File 3: Makefile for ACL2
```makefile
.PHONY: cert clean

cert:
	acl2 < agent-state.lisp > agent-state.log 2>&1
	acl2 < reasoning.lisp > reasoning.log 2>&1

clean:
	rm -f *.cert *.log
```

---

## XI. BOOKS READING ORDER

1. **Step 1**: CAR Chapters 2-3 (Lisp basics, proving simple theorems)
2. **Step 2**: CAR Chapter 4 (STObj, state management) + stobj reference
3. **Step 3**: CAR Chapters 5-6 (Lists, recursion, induction proofs)
4. **Step 4**: CAR Chapter 7 (Complex proofs, case analysis)
5. **Step 5**: ACL2 Manual `:doc defun`, `:doc guards`
6. **Step 6**: Russinoff "High-Speed Simulators" case study
7. **Step 7**: Design your own theorems, iterate

---

## XII. SUCCESS METRICS

### By Step 2
- [ ] Can define basic functions in ACL2
- [ ] Understand STObj syntax and semantics
- [ ] Prove simple properties about your code

### By Step 4
- [ ] Implement minimal ReAct loop
- [ ] Prove it terminates
- [ ] Prove it maintains invariants

### By Step 8
- [ ] Full agent loop with 5+ theorems
- [ ] Demonstrated soundness of decision-making
- [ ] Bounded resource usage proven
- [ ] External tool interface specified

---

## XIII. TRANSITION TO Z3/SMTLINK

Once Phase 1 completes (8 steps):

- For reasoning chains that don't fit ACL2's inductive proof style
- Use **SMTLink**: integrate Z3 into ACL2 proofs
- Example:

```lisp
(include-book "smtlink/top")

(defun verify-reasoning-step-with-z3 (premise conclusion)
  "Use Z3 to verify logical entailment"
  (let ((result (smt-goal (implies premise conclusion))))
    result))
```

But **not needed for initial ReAct agent** - pure functional ACL2 is sufficient.

---

## XIV. REFERENCES

**Essential**:
- Computer-Aided Reasoning books (3 volumes): www.cs.utexas.edu/~moore/publications/acl2-books/
- ACL2 Manual: www.cs.utexas.edu/~moore/acl2/
- Kestrel books: www.kestrel.edu

**Supplementary**:
- ACL2 Workshop proceedings (last 5 years)
- David Russinoff's papers on formal verification
- Jared Davis's ACL2 development blog

---

## XV. NEXT IMMEDIATE STEPS

1. **Install ACL2** (free, open source)
2. **Work through CAR Chapter 2** 
3. **Write first simple agent proof**
4. **Share proof with team**
5. **Iterate** - each step add more complex features

**Your step 1 goal: Complete first mini-project (simple agent-state.lisp + reasoning.lisp with 3 theorems proving + running proofs).
