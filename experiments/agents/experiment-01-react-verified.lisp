; Verified ReAct Agent with Z3 Enforcement & Optimization
;
; This experiment defines a ReAct-style chain-of-thought agent where:
; 1. Tool permissions (file access + execute) are formally specified
; 2. LLM and tool costs (tokens, time, money) are constrained
; 3. Z3 enforces constraints AND optimizes continue-vs-respond decisions
; 4. Guards are verified to ensure type safety
;
; Building incrementally with guard verification at each step.

(in-package "ACL2")

;;; ==========================================================================
;;; Part 1: Permission Model (Orthogonal: File Access + Execute)
;;; ==========================================================================

; File access levels (ordered enum for comparison)
(defconst *access-none* 0)
(defconst *access-read* 1)
(defconst *access-read-write* 2)

; Permission level predicate - guard is t (accepts anything)
(defun access-level-p (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x 2)))

; Theorem: access-level-p implies natp (useful for later guards)
(defthm access-level-p-implies-natp
  (implies (access-level-p x)
           (natp x))
  :rule-classes :forward-chaining)

; Check if granted access is sufficient for required access
; Both inputs must be valid access levels
(defun access-sufficient-p (required granted)
  (declare (xargs :guard (and (access-level-p required)
                              (access-level-p granted))))
  (<= required granted))

; Full permission check: file access + execute
; Execute is orthogonal - tools that execute code need execute permission
(defun tool-permitted-p (required-access requires-execute granted-access execute-allowed)
  (declare (xargs :guard (and (access-level-p required-access)
                              (booleanp requires-execute)
                              (access-level-p granted-access)
                              (booleanp execute-allowed))))
  (and (access-sufficient-p required-access granted-access)
       (implies requires-execute execute-allowed)))

;;; ==========================================================================
;;; Part 2: LLM Model Specification
;;; ==========================================================================

; LLM model specification as a simple list structure
; (name tokens-per-second cost-per-1k-input cost-per-1k-output)
; Using positive rationals for rates and costs

(defun llm-model-spec-p (spec)
  (declare (xargs :guard t))
  (and (true-listp spec)
       (eql (len spec) 4)
       (stringp (nth 0 spec))                          ; name
       (rationalp (nth 1 spec)) (< 0 (nth 1 spec))     ; tokens-per-second > 0
       (rationalp (nth 2 spec)) (<= 0 (nth 2 spec))    ; cost-per-1k-input >= 0
       (rationalp (nth 3 spec)) (<= 0 (nth 3 spec))))  ; cost-per-1k-output >= 0

; Accessors with verified guards
(defun llm-model-name (spec)
  (declare (xargs :guard (llm-model-spec-p spec)))
  (nth 0 spec))

(defun llm-model-tps (spec)
  (declare (xargs :guard (llm-model-spec-p spec)))
  (nth 1 spec))

(defun llm-model-cost-input (spec)
  (declare (xargs :guard (llm-model-spec-p spec)))
  (nth 2 spec))

(defun llm-model-cost-output (spec)
  (declare (xargs :guard (llm-model-spec-p spec)))
  (nth 3 spec))

; Theorems about accessor return types (for downstream guard proofs)
(defthm llm-model-tps-positive
  (implies (llm-model-spec-p spec)
           (and (rationalp (llm-model-tps spec))
                (< 0 (llm-model-tps spec))))
  :rule-classes :forward-chaining)

(defthm llm-model-cost-input-rational
  (implies (llm-model-spec-p spec)
           (and (rationalp (llm-model-cost-input spec))
                (<= 0 (llm-model-cost-input spec))))
  :rule-classes :forward-chaining)

(defthm llm-model-cost-output-rational
  (implies (llm-model-spec-p spec)
           (and (rationalp (llm-model-cost-output spec))
                (<= 0 (llm-model-cost-output spec))))
  :rule-classes :forward-chaining)

;;; ==========================================================================
;;; Part 3: LLM Cost Calculations
;;; ==========================================================================

; Calculate LLM call cost in millicents
; Returns a non-negative rational
(defun llm-call-cost (spec input-tokens output-tokens)
  (declare (xargs :guard (and (llm-model-spec-p spec)
                              (natp input-tokens)
                              (natp output-tokens))))
  (+ (* (/ input-tokens 1000) (llm-model-cost-input spec))
     (* (/ output-tokens 1000) (llm-model-cost-output spec))))

; Calculate LLM call time in milliseconds
; Returns a non-negative rational
(defun llm-call-time-ms (spec input-tokens output-tokens)
  (declare (xargs :guard (and (llm-model-spec-p spec)
                              (natp input-tokens)
                              (natp output-tokens))))
  (* 1000 (/ (+ input-tokens output-tokens) (llm-model-tps spec))))

; Theorems about cost calculation return types
(defthm llm-call-cost-rational
  (implies (and (llm-model-spec-p spec)
                (natp input-tokens)
                (natp output-tokens))
           (and (rationalp (llm-call-cost spec input-tokens output-tokens))
                (<= 0 (llm-call-cost spec input-tokens output-tokens))))
  :hints (("Goal" :in-theory (enable llm-call-cost))))

(defthm llm-call-time-ms-rational
  (implies (and (llm-model-spec-p spec)
                (natp input-tokens)
                (natp output-tokens))
           (and (rationalp (llm-call-time-ms spec input-tokens output-tokens))
                (<= 0 (llm-call-time-ms spec input-tokens output-tokens))))
  :hints (("Goal" :in-theory (enable llm-call-time-ms))))

;;; ==========================================================================
;;; Part 4: Tool Specification
;;; ==========================================================================

; Tool specification as a simple list structure
; (name required-access requires-execute base-cost time-estimate token-estimate)

(defun tool-spec-p (spec)
  (declare (xargs :guard t))
  (and (true-listp spec)
       (eql (len spec) 6)
       (stringp (nth 0 spec))           ; name
       (access-level-p (nth 1 spec))    ; required-file-access
       (booleanp (nth 2 spec))          ; requires-execute
       (natp (nth 3 spec))              ; base-cost (millicents)
       (natp (nth 4 spec))              ; time-estimate-ms
       (natp (nth 5 spec))))            ; token-estimate

; Accessors with verified guards
(defun tool-name (spec)
  (declare (xargs :guard (tool-spec-p spec)))
  (nth 0 spec))

(defun tool-required-access (spec)
  (declare (xargs :guard (tool-spec-p spec)))
  (nth 1 spec))

(defun tool-requires-execute (spec)
  (declare (xargs :guard (tool-spec-p spec)))
  (nth 2 spec))

(defun tool-base-cost (spec)
  (declare (xargs :guard (tool-spec-p spec)))
  (nth 3 spec))

(defun tool-time-estimate (spec)
  (declare (xargs :guard (tool-spec-p spec)))
  (nth 4 spec))

(defun tool-token-estimate (spec)
  (declare (xargs :guard (tool-spec-p spec)))
  (nth 5 spec))

; Return type theorems for tool accessors
(defthm tool-required-access-type
  (implies (tool-spec-p spec)
           (access-level-p (tool-required-access spec)))
  :rule-classes :forward-chaining)

(defthm tool-requires-execute-type
  (implies (tool-spec-p spec)
           (booleanp (tool-requires-execute spec)))
  :rule-classes :forward-chaining)

(defthm tool-base-cost-type
  (implies (tool-spec-p spec)
           (natp (tool-base-cost spec)))
  :rule-classes :forward-chaining)

(defthm tool-time-estimate-type
  (implies (tool-spec-p spec)
           (natp (tool-time-estimate spec)))
  :rule-classes :forward-chaining)

(defthm tool-token-estimate-type
  (implies (tool-spec-p spec)
           (natp (tool-token-estimate spec)))
  :rule-classes :forward-chaining)

;;; ==========================================================================
;;; Part 5: Agent State
;;; ==========================================================================

; Agent state as a list structure
; (iteration max-iterations token-budget cost-budget time-budget 
;  file-access execute-allowed satisfaction done)

(defun agent-state-p (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (eql (len st) 9)
       (natp (nth 0 st))              ; iteration
       (natp (nth 1 st))              ; max-iterations
       (natp (nth 2 st))              ; token-budget-remaining
       (natp (nth 3 st))              ; cost-budget-remaining (millicents)
       (natp (nth 4 st))              ; time-budget-remaining-ms
       (access-level-p (nth 5 st))    ; granted-file-access
       (booleanp (nth 6 st))          ; execute-allowed
       (rationalp (nth 7 st))         ; satisfaction-score
       (<= 0 (nth 7 st))
       (<= (nth 7 st) 1)
       (booleanp (nth 8 st))))        ; done

; Accessors
(defun agent-iteration (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 0 st))

(defun agent-max-iterations (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 1 st))

(defun agent-token-budget (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 2 st))

(defun agent-cost-budget (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 3 st))

(defun agent-time-budget (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 4 st))

(defun agent-file-access (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 5 st))

(defun agent-execute-allowed (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 6 st))

(defun agent-satisfaction (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 7 st))

(defun agent-done (st)
  (declare (xargs :guard (agent-state-p st)))
  (nth 8 st))

; Return type theorems for agent accessors
(defthm agent-iteration-type
  (implies (agent-state-p st)
           (natp (agent-iteration st)))
  :rule-classes :forward-chaining)

(defthm agent-max-iterations-type
  (implies (agent-state-p st)
           (natp (agent-max-iterations st)))
  :rule-classes :forward-chaining)

(defthm agent-token-budget-type
  (implies (agent-state-p st)
           (natp (agent-token-budget st)))
  :rule-classes :forward-chaining)

(defthm agent-cost-budget-type
  (implies (agent-state-p st)
           (natp (agent-cost-budget st)))
  :rule-classes :forward-chaining)

(defthm agent-time-budget-type
  (implies (agent-state-p st)
           (natp (agent-time-budget st)))
  :rule-classes :forward-chaining)

(defthm agent-file-access-type
  (implies (agent-state-p st)
           (access-level-p (agent-file-access st)))
  :rule-classes :forward-chaining)

(defthm agent-execute-allowed-type
  (implies (agent-state-p st)
           (booleanp (agent-execute-allowed st)))
  :rule-classes :forward-chaining)

(defthm agent-satisfaction-type
  (implies (agent-state-p st)
           (and (rationalp (agent-satisfaction st))
                (<= 0 (agent-satisfaction st))
                (<= (agent-satisfaction st) 1)))
  :rule-classes :forward-chaining)

(defthm agent-done-type
  (implies (agent-state-p st)
           (booleanp (agent-done st)))
  :rule-classes :forward-chaining)

; Constructor
(defun make-agent-state (iter max-iter tokens cost time-ms access exec sat done)
  (declare (xargs :guard (and (natp iter)
                              (natp max-iter)
                              (natp tokens)
                              (natp cost)
                              (natp time-ms)
                              (access-level-p access)
                              (booleanp exec)
                              (rationalp sat)
                              (<= 0 sat)
                              (<= sat 1)
                              (booleanp done))))
  (list iter max-iter tokens cost time-ms access exec sat done))

; Constructor produces valid state
(defthm make-agent-state-valid
  (implies (and (natp iter)
                (natp max-iter)
                (natp tokens)
                (natp cost)
                (natp time-ms)
                (access-level-p access)
                (booleanp exec)
                (rationalp sat)
                (<= 0 sat)
                (<= sat 1)
                (booleanp done))
           (agent-state-p (make-agent-state iter max-iter tokens cost time-ms access exec sat done))))

;;; ==========================================================================
;;; Part 6: Budget Checking
;;; ==========================================================================

; Check if there's sufficient budget for a tool call
(defun tool-budget-sufficient-p (st tool)
  (declare (xargs :guard (and (agent-state-p st)
                              (tool-spec-p tool))))
  (and (<= (tool-base-cost tool) (agent-cost-budget st))
       (<= (tool-time-estimate tool) (agent-time-budget st))
       (<= (tool-token-estimate tool) (agent-token-budget st))))

; Check if tool is both permitted and within budget
(defun can-invoke-tool-p (st tool)
  (declare (xargs :guard (and (agent-state-p st)
                              (tool-spec-p tool))))
  (and (tool-permitted-p (tool-required-access tool)
                         (tool-requires-execute tool)
                         (agent-file-access st)
                         (agent-execute-allowed st))
       (tool-budget-sufficient-p st tool)))

;;; ==========================================================================
;;; Part 7: State Transitions
;;; ==========================================================================

; Deduct tool call costs from state
(defun deduct-tool-cost (st tool)
  (declare (xargs :guard (and (agent-state-p st)
                              (tool-spec-p tool))))
  (make-agent-state
   (agent-iteration st)
   (agent-max-iterations st)
   (nfix (- (agent-token-budget st) (tool-token-estimate tool)))
   (nfix (- (agent-cost-budget st) (tool-base-cost tool)))
   (nfix (- (agent-time-budget st) (tool-time-estimate tool)))
   (agent-file-access st)
   (agent-execute-allowed st)
   (agent-satisfaction st)
   (agent-done st)))

; Deduct-tool-cost preserves state validity
(defthm deduct-tool-cost-valid
  (implies (and (agent-state-p st)
                (tool-spec-p tool))
           (agent-state-p (deduct-tool-cost st tool))))

; Update satisfaction score (from LLM-as-judge)
(defun update-satisfaction (st new-score)
  (declare (xargs :guard (and (agent-state-p st)
                              (rationalp new-score)
                              (<= 0 new-score)
                              (<= new-score 1))))
  (make-agent-state
   (agent-iteration st)
   (agent-max-iterations st)
   (agent-token-budget st)
   (agent-cost-budget st)
   (agent-time-budget st)
   (agent-file-access st)
   (agent-execute-allowed st)
   new-score
   (agent-done st)))

(defthm update-satisfaction-valid
  (implies (and (agent-state-p st)
                (rationalp new-score)
                (<= 0 new-score)
                (<= new-score 1))
           (agent-state-p (update-satisfaction st new-score))))

; Mark agent as done
(defun mark-done (st)
  (declare (xargs :guard (agent-state-p st)))
  (make-agent-state
   (agent-iteration st)
   (agent-max-iterations st)
   (agent-token-budget st)
   (agent-cost-budget st)
   (agent-time-budget st)
   (agent-file-access st)
   (agent-execute-allowed st)
   (agent-satisfaction st)
   t))

(defthm mark-done-valid
  (implies (agent-state-p st)
           (agent-state-p (mark-done st))))

; Increment iteration (after LLM call)
(defun increment-iteration (st)
  (declare (xargs :guard (agent-state-p st)))
  (make-agent-state
   (1+ (agent-iteration st))
   (agent-max-iterations st)
   (agent-token-budget st)
   (agent-cost-budget st)
   (agent-time-budget st)
   (agent-file-access st)
   (agent-execute-allowed st)
   (agent-satisfaction st)
   (agent-done st)))

(defthm increment-iteration-valid
  (implies (agent-state-p st)
           (agent-state-p (increment-iteration st))))

(defthm increment-iteration-increases
  (implies (agent-state-p st)
           (< (agent-iteration st)
              (agent-iteration (increment-iteration st)))))

;;; ==========================================================================
;;; Part 8: Continue vs Respond Decision
;;; ==========================================================================

; Minimum budget thresholds
(defconst *min-llm-tokens* 100)
(defconst *min-iteration-cost* 10)
(defconst *min-iteration-time* 1000)
(defconst *satisfaction-threshold* 9/10)

; Must respond: no budget for another iteration OR done OR max iterations
(defun must-respond-p (st)
  (declare (xargs :guard (agent-state-p st)))
  (or (agent-done st)
      (>= (agent-iteration st) (agent-max-iterations st))
      (< (agent-token-budget st) *min-llm-tokens*)
      (< (agent-cost-budget st) *min-iteration-cost*)
      (< (agent-time-budget st) *min-iteration-time*)))

; Should continue: has budget and below satisfaction threshold
(defun should-continue-p (st)
  (declare (xargs :guard (agent-state-p st)))
  (and (not (must-respond-p st))
       (< (agent-satisfaction st) *satisfaction-threshold*)))

;;; ==========================================================================
;;; Part 9: Key Theorems
;;; ==========================================================================

; Theorem: Permission safety - can-invoke-tool-p implies tool-permitted-p
(defthm permission-safety
  (implies (and (agent-state-p st)
                (tool-spec-p tool)
                (can-invoke-tool-p st tool))
           (tool-permitted-p (tool-required-access tool)
                             (tool-requires-execute tool)
                             (agent-file-access st)
                             (agent-execute-allowed st))))

; Theorem: Budget non-negativity after tool deduction
(defthm tool-deduction-preserves-budget-nonneg
  (implies (and (agent-state-p st)
                (tool-spec-p tool))
           (and (natp (agent-token-budget (deduct-tool-cost st tool)))
                (natp (agent-cost-budget (deduct-tool-cost st tool)))
                (natp (agent-time-budget (deduct-tool-cost st tool))))))

; Theorem: Iteration strictly increases
(defthm iteration-increases
  (implies (agent-state-p st)
           (< (agent-iteration st)
              (agent-iteration (increment-iteration st)))))

; Theorem: After enough iterations, must-respond becomes true
; (Termination guarantee via iteration bound)
(defthm termination-by-iteration
  (implies (and (agent-state-p st)
                (>= (agent-iteration st) (agent-max-iterations st)))
           (must-respond-p st)))

