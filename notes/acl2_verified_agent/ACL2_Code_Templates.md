# ACL2 Verified Agent: Code Templates & References

## Quick Reference: ACL2 Constructs for Agents

### 1. DEFINING AGENT STATE (STObj)

**Pattern**: Single-threaded object for mutable agent state

```lisp
(defstobj my-agent
  ; Field name : type specification : initial value
  (facts :type (array t (1000)))           ; Knowledge base
  (num-facts :type (integer 0 *) :initially 0)
  (beliefs :type (array rational (1000)))  ; Confidence scores
  (goal-stack :type (array t (100)))       ; Active goals
  (num-goals :type (integer 0 *) :initially 0)
  (step-counter :type (integer 0 1000000) :initially 0)
  (max-steps :type (integer 0 1000000) :initially 10000)
  (error-state :type symbol :initially nil))

; Accessor syntax: (field-name agent)
; Mutator syntax: (update-field-name value agent)

; Example: Add a fact
(defun add-fact (fact ag)
  (declare (xargs :stobjs ag))
  (let* ((n (num-facts ag))
         (ag (update-facts n fact ag))
         (ag (update-num-facts (+ 1 n) ag)))
    ag))

; Example: Check fact
(defun has-fact-p (fact ag)
  (declare (xargs :stobjs ag))
  (loop for i from 0 to (- (num-facts ag) 1)
        when (equal (facts ag i) fact)
        return t
        finally (return nil)))
```

**Key points**:
- `:type (array t (N))` = array of any type, size N
- `:type (integer 0 *)` = bounded counter
- Functions taking stobj must declare `:stobjs ag`
- Functions return modified stobj: `ag` or `(mv result ag)`

---

### 2. REASONING FUNCTIONS (Pure Logic)

**Pattern**: Decision-making as pure functions (no stobj)

```lisp
; Determine if goal is achieved
(defun goal-satisfied-p (goal facts)
  "Check if goal appears in facts"
  (member goal facts))

; Select best action given current situation
(defun choose-action (facts goals)
  "Deterministic action selection logic"
  (cond
    ((null goals) 'idle)
    ((goal-satisfied-p (car goals) facts) 
     (make-action :type 'achieve-goal :goal (car goals)))
    (t (make-action :type 'query-external :query (car goals)))))

; Verify action is safe to execute
(defun action-preconditions-met-p (action facts)
  "Check if action can be executed"
  (case (action-type action)
    (achieve-goal (goal-satisfied-p (action-goal action) facts))
    (query-external (and (not (null (action-query action)))
                        (< (length facts) 1000)))
    (t nil)))

; Example theorem
(defthm action-is-deterministic
  (implies (and (true-listp facts1)
                (equal facts1 facts2)
                (equal goals1 goals2))
           (equal (choose-action facts1 goals1)
                  (choose-action facts2 goals2))))
```

**Key points**:
- No stobj here = logically pure = easily provable
- All decisions are functions of facts and goals
- Preconditions are checkable predicates

---

### 3. STATE OBSERVATION (Integrating External Responses)

**Pattern**: Update agent beliefs from external tool response

```lisp
; Process response from external tool
(defun integrate-response (response facts)
  "Add new facts from external response"
  (if (valid-response-p response)
      (append facts (extract-facts-from-response response))
      facts))  ; Ignore invalid responses

; Update agent with observation
(defun process-external-response (response ag)
  (declare (xargs :stobjs ag))
  (let* ((new-facts (extract-facts-from-response response))
         (ag (loop for fact in new-facts
                   do (setf ag (add-fact fact ag)))))
    ag))

; Example: Safe observation processing
(defun safe-observe (response belief-state ag)
  (declare (xargs :stobjs ag))
  (cond
    ((not (valid-response-p response)) 
     (let ((ag (update-error-state 'bad-response ag)))
       ag))
    ((too-many-facts-p ag)
     (update-error-state 'memory-full ag))
    (t (process-external-response response ag))))

; Theorem: Observation doesn't lose facts
(defthm observation-preserves-facts
  (implies (and (member fact facts)
                (valid-response-p response))
           (member fact (integrate-response response facts))))
```

---

### 4. MAIN LOOP (Combining Everything)

**Pattern**: ReAct cycle with bounded iterations

```lisp
; One iteration of ReAct cycle
(defun react-step (ag)
  (declare (xargs :stobjs ag))
  (let* ((current-goal (car (get-goals ag)))
         (facts (get-facts ag))
         
         ; Think: what action to take?
         (action (choose-action facts (list current-goal)))
         
         ; Verify: safe to execute?
         (safe-p (action-preconditions-met-p action facts)))
    
    (cond
      ((not safe-p)
       ; Precondition failed, record error
       (let ((ag (update-step-counter (+ 1 (step-counter ag)) ag)))
         (update-error-state 'precondition-failed ag)))
      
      (t
       ; Safe: record action (would call external tool here)
       (let ((ag (update-step-counter (+ 1 (step-counter ag)) ag)))
         ag)))))

; Main loop: iterate until goal or max steps
(defun agent-loop (ag)
  (declare (xargs :stobjs ag
                  :measure (nfix (- (max-steps ag) 
                                   (step-counter ag)))))
  (cond
    ((>= (step-counter ag) (max-steps ag)) ag)
    ((null (goal-stack-to-list ag)) ag)  ; No more goals
    ((error-state ag) ag)                 ; Error encountered
    (t (let ((ag (react-step ag)))
         (agent-loop ag)))))

; Theorem: loop terminates
(defthm agent-loop-terminates
  (implies (and (my-agent-p ag)
                (natp (max-steps ag)))
           (my-agent-p (agent-loop ag))))

; Theorem: step counter doesn't exceed limit
(defthm step-counter-bounded
  (implies (and (my-agent-p ag)
                (<= initial-steps (max-steps ag)))
           (<= (step-counter (agent-loop ag))
               (max-steps ag))))
```

---

### 5. THEOREMS TEMPLATE

**Pattern**: Proving properties about your agent

```lisp
; Soundness: if we decide to act, preconditions hold
(defthm agent-decisions-are-sound
  (implies (and (my-agent-p ag)
                (equal (choose-action facts goals) action)
                (not (null action)))
           (action-preconditions-met-p action facts)))

; Progress: agent makes progress toward goal
(defthm agent-progress
  (implies (and (my-agent-p ag)
                (member goal (goal-stack-to-list ag))
                (null (error-state ag)))
           (or (member goal (get-facts (agent-loop ag)))
               (>= (step-counter (agent-loop ag))
                   (max-steps ag)))))

; Safety: agent never violates policies
(defthm agent-respects-policies
  (implies (and (my-agent-p ag)
                (policy-p policy)
                (policy-satisfied-p ag policy))
           (policy-satisfied-p (agent-loop ag) policy)))

; Idempotence: re-running from same state yields same result
(defthm agent-deterministic
  (implies (and (my-agent-p ag1)
                (equal (get-facts ag1) (get-facts ag2))
                (equal (goal-stack-to-list ag1)
                       (goal-stack-to-list ag2)))
           (equal (agent-loop ag1) (agent-loop ag2))))
```

---

### 6. GUARDS & GUARD VERIFICATION

**Pattern**: Prove type safety at compile time

```lisp
(defun process-fact (fact facts)
  (declare (xargs :guard (and (atom fact)
                              (true-listp facts))
                  :verify-guards nil))
  (cons fact facts))

; Later, after you prove it's correct:
(verify-guards process-fact)

; Guards on stobj operations
(defun safe-add-fact (fact ag)
  (declare (xargs :stobjs ag
                  :guard (and (my-agent-p ag)
                              (atom fact)
                              (< (num-facts ag) 1000))))
  (let* ((ag (update-facts (num-facts ag) fact ag))
         (ag (update-num-facts (+ 1 (num-facts ag)) ag)))
    ag))
```

---

### 7. ENCAPSULATION (Abstract Tool Specs)

**Pattern**: Define abstract external tool, prove theorems about it

```lisp
(encapsulate ((external-llm-call (query facts) t))
  
  ; Local stub implementation
  (local (defun external-llm-call (query facts)
           (declare (ignore query facts))
           '(fact1 fact2)))  ; Always returns something
  
  ; Specification: what we assume about the oracle
  (defthm external-call-always-succeeds
    (let ((response (external-llm-call query facts)))
      (true-listp response)))
  
  (defthm external-call-bounded
    (implies (and (atom query)
                  (true-listp facts))
             (< (length (external-llm-call query facts))
                1000))))

; Now ANY implementation of external-llm-call works
; Agent theorems hold REGARDLESS of which LLM we use
```

---

### 8. KEY PATTERNS FOR DIFFERENT SCENARIOS

#### Pattern A: Iterating Over STObj Array

```lisp
(defun collect-facts (ag)
  (declare (xargs :stobjs ag))
  (loop for i from 0 to (- (num-facts ag) 1)
        collect (facts ag i)))

; Theorem: collection is non-empty if facts exist
(defthm facts-collection-matches-count
  (implies (< 0 (num-facts ag))
           (< 0 (length (collect-facts ag)))))
```

#### Pattern B: Multi-Valued Returns

```lisp
(defun agent-decide-and-update (ag)
  (declare (xargs :stobjs ag))
  (let* ((decision (choose-action (get-facts ag) (get-goals ag)))
         (ag (update-step-counter (+ 1 (step-counter ag)) ag)))
    (mv decision ag)))  ; Return both decision AND updated state

; Using multi-valued return
(mv-let (decision new-ag)
  (agent-decide-and-update ag)
  (process-decision decision new-ag))
```

#### Pattern C: Conditional Updates

```lisp
(defun maybe-add-fact (fact ag)
  (declare (xargs :stobjs ag))
  (if (and (not (has-fact-p fact ag))
           (< (num-facts ag) 1000))
      (add-fact fact ag)
      ag))  ; Return unchanged if can't add

; Theorem: add only happens under conditions
(defthm maybe-add-fact-increases-or-not
  (or (equal (num-facts (maybe-add-fact f ag))
             (+ 1 (num-facts ag)))
      (equal (num-facts (maybe-add-fact f ag))
             (num-facts ag))))
```

#### Pattern D: Measure-Based Recursion

```lisp
(defun search-for-fact (target facts n)
  (declare (xargs :measure (nfix (- (length facts) n))))
  (cond
    ((>= n (length facts)) nil)
    ((equal target (nth n facts)) n)
    (t (search-for-fact target facts (+ 1 n)))))

; Theorem: if found, returns valid index
(defthm search-finds-position
  (implies (member x facts)
           (< (search-for-fact x facts 0)
              (length facts))))
```

---

### 9. TESTING THEOREM HYPOTHESES

Before committing to a theorem, test it:

```lisp
; Test: does this hold?
(thm (implies (and (true-listp facts)
                   (member goal facts))
              (goal-satisfied-p goal facts)))

; If it fails, ACL2 shows counterexample
; If it succeeds, you can promote to defthm
(defthm goal-satisfied-iff-member
  (implies (true-listp facts)
           (iff (goal-satisfied-p goal facts)
                (member goal facts))))
```

---

### 10. PROOF HINTS

When proofs get stuck, use hints:

```lisp
(defthm complex-theorem
  (implies (and (my-agent-p ag)
                (valid-facts facts))
           (conclusion ag facts))
  :hints (("Goal" 
           :do-not-induct nil
           :induct (custom-induction-scheme ag)
           :use ((:instance helper-lemma (x facts)))
           :cases ((null facts) (consp facts))))
         ("Subgoal 1"
          :simp :rewrite helper-rules)
         ("Subgoal 2"
          :arith)))  ; Use linear arithmetic solver
```

---

## REFERENCE: ACL2 Documentation Topics

**Essential to read** (in order):

1. `:doc defun` - How to define functions
2. `:doc declare` - xargs and other declarations
3. `:doc defstobj` - Single-threaded objects (CRITICAL)
4. `:doc defthm` - Proving theorems
5. `:doc induction` - Proof by induction
6. `:doc hints` - Proof hints and guidance
7. `:doc guard` - Type safety and guards
8. `:doc loop$` - Loop constructs

**For learning**:

- `:doc tutorial` - Guided introduction
- `:doc proof-by-induction-for-recursive-functions`
- `:doc case-analysis-in-inductive-proofs`

---

## Quick Start: Copy-Paste Skeleton

```lisp
(in-package "ACL2")

; === Agent State ===
(defstobj my-ag
  (facts :type (array t (100)))
  (num-facts :type (integer 0 *) :initially 0)
  (goals :type (array t (50)))
  (num-goals :type (integer 0 *) :initially 0)
  (steps :type (integer 0 *) :initially 0))

; === Helper Predicates ===
(defun has-fact (f ag)
  (declare (xargs :stobjs ag))
  (loop for i from 0 to (- (num-facts ag) 1)
        when (equal (facts ag i) f)
        return t
        finally (return nil)))

; === Reasoning ===
(defun think (ag)
  (if (has-fact 'goal-achieved ag)
      'success
      'continue))

; === Action Selection ===
(defun select-action (ag)
  (case (think ag)
    (success 'stop)
    (t 'query)))

; === One Step ===
(defun step (ag)
  (declare (xargs :stobjs ag))
  (update-steps (+ 1 (steps ag)) ag))

; === Main Loop ===
(defun run (ag max-steps)
  (declare (xargs :stobjs ag
                  :measure (nfix (- max-steps (steps ag)))))
  (cond
    ((>= (steps ag) max-steps) ag)
    ((equal (think ag) 'success) ag)
    (t (run (step ag) max-steps))))

; === Theorems ===
(defthm run-terminates
  (implies (and (my-ag-p ag) (natp n))
           (my-ag-p (run ag n))))

(defthm steps-bounded
  (implies (and (my-ag-p ag)
                (<= (steps ag) n))
           (<= (steps (run ag n)) n)))
```

Save as `agent.lisp`, then:
```bash
acl2 < agent.lisp
```

ACL2 will prove your theorems!

---

## Common Mistakes to Avoid

1. **Forgetting :stobjs in declare**
   ```lisp
   ; WRONG:
   (defun bad (f ag) (add-fact f ag))
   
   ; RIGHT:
   (defun good (f ag)
     (declare (xargs :stobjs ag))
     (add-fact f ag))
   ```

2. **Trying to prove something false**
   - If `(thm ...)` fails, it's probably not true
   - Simplify hypothesis or add cases

3. **Not providing measure for recursion**
   ```lisp
   ; WRONG:
   (defun loop (ag)
     (loop ag))  ; Infinite loop!
   
   ; RIGHT:
   (defun loop (ag)
     (declare (xargs :measure (nfix (- max (steps ag)))))
     (if (>= (steps ag) max) ag
         (loop (step ag))))
   ```

4. **Mixing stobj and non-stobj operations**
   - Functions either take stobj or don't
   - Can't mix `ag` and modified values

5. **Not initializing stobj fields**
   ```lisp
   ; Specify initial values!
   (defstobj ag
     (field :type integer :initially 0))
   ```

---

## Debugging Failed Proofs

**When a theorem won't prove**:

1. First: Use `(thm ...)` to test in interactive mode
2. Check: Are the hypotheses actually required?
   - Remove hypotheses one by one
3. Examine: What's the failing subgoal?
   - Look for pattern ACL2 can't simplify
4. Try cases: Does it need case analysis?
   - Add `:cases ((cond1) (cond2))`
5. Look for lemmas: Do you need to prove helper facts first?
   - Build lemmas from bottom up

**Example**:
```lisp
; This fails
(thm (implies (true-listp x) (equal (length x) 5)))

; Why? Length isn't always 5
; Fix: add actual constraint
(thm (implies (and (true-listp x)
                   (equal (length x) 5))
              (equal (length x) 5)))  ; Now trivial
```

---

## Books You Can Include

Most useful libraries:

```lisp
(include-book "std/lists/top" :dir :system)  ; List operations
(include-book "std/util/define" :dir :system) ; Modern defun
(include-book "std/stobjs/top" :dir :system) ; STObj utilities
(include-book "arithmetic-5/top" :dir :system) ; Arithmetic

; For more advanced work:
(include-book "projects/apply-dollar/apply-dollar") ; Higher-order functions
(include-book "centaur/fgl/top" :dir :system) ; SAT-based verification
```

All available in your ACL2 distribution.

---

**End of Reference**

You now have everything you need to start building verified agents in ACL2!
