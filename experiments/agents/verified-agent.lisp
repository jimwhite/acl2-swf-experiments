; verified-agent.lisp - Verified ReAct Agent in ACL2
; 
; A formally verified agent using FTY types that proves:
; - Permission safety: can-invoke implies tool-permitted
; - Budget bounds: budgets remain non-negative after deductions
; - Termination: agent halts within max-steps
; - Error handling: errors force must-respond
; - State coverage: agent either continues, must respond, or is satisfied
;
; External tools (Oxigraph KG, Qdrant vectors, LLM) accessed via MCP.
; ACL2 proves properties about decision logic, not external systems.

(in-package "ACL2")

;;;============================================================================
;;; Part 1: Library Imports
;;;============================================================================

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "llm-types")  ; chat-message-list-p, model-info-p

;;;============================================================================
;;; Part 2: Error Types
;;;============================================================================

;; Structured error kinds for rich error handling
(fty::deftagsum error-kind
  (:none ())
  (:resource-exhausted ())
  (:precondition-failed ((reason stringp)))
  (:tool-error ((tool-name symbolp) (message stringp)))
  (:max-iterations ())
  :layout :list)

;;;============================================================================
;;; Part 3: Tool Specification
;;;============================================================================

;; Tool specification - describes a tool's requirements
(fty::defprod tool-spec
  ((name symbolp)
   (required-access natp :default 0)      ; 0=none, 1=read, 2=read-write
   (requires-execute booleanp :default nil)
   (token-cost natp :default 0)
   (time-cost natp :default 0))
  :layout :list)

;;;============================================================================
;;; Part 4: Agent State
;;;============================================================================

;; Core agent state - tracks resources, permissions, conversation, and status
(fty::defprod agent-state
  (;; Step and resource management
   (step-counter natp :default 0)
   (max-steps natp :default 100)
   (token-budget natp :default 10000)
   (time-budget natp :default 3600)
   ;; Permissions
   (file-access natp :default 0)          ; granted access level (0/1/2)
   (execute-allowed booleanp :default nil)
   ;; Conversation history (for LLM context)
   (messages chat-message-list-p :default nil)
   (max-context-tokens natp :default 8000) ; from model-info->loaded-context-length
   (system-prompt stringp :default "")     ; cached for reference
   ;; Completion status
   (satisfaction natp :default 0)         ; 0-100 scale
   (done booleanp :default nil)
   (error-state error-kind-p :default '(:none)))
  :layout :list)

;;;============================================================================
;;; Part 5: Action Types  
;;;============================================================================

;; Actions the agent can take
(fty::deftagsum agent-action
  (:tool-call ((tool-name symbolp) (query stringp)))
  (:final-answer ((answer stringp)))
  (:no-action ())
  :layout :list)

;;;============================================================================
;;; Part 6: Constants
;;;============================================================================

(defconst *satisfaction-threshold* 100)

;; Access level constants
(defconst *access-none* 0)
(defconst *access-read* 1)
(defconst *access-read-write* 2)

;;;============================================================================
;;; Part 7: Pure Decision Functions
;;;============================================================================

;; Check if granted access is sufficient for required access
(define access-sufficient-p ((required natp) (granted natp))
  :returns (result booleanp)
  (<= required granted))

;; Check if tool permissions are satisfied
(define tool-permitted-p ((tool tool-spec-p) (st agent-state-p))
  :returns (result booleanp)
  (b* ((required-access (tool-spec->required-access tool))
       (requires-exec (tool-spec->requires-execute tool))
       (granted-access (agent-state->file-access st))
       (exec-allowed (agent-state->execute-allowed st)))
    (and (access-sufficient-p required-access granted-access)
         (or (not requires-exec) exec-allowed))))

;; Check if budget is sufficient for tool
(define tool-budget-sufficient-p ((tool tool-spec-p) (st agent-state-p))
  :returns (result booleanp)
  (b* ((token-cost (tool-spec->token-cost tool))
       (time-cost (tool-spec->time-cost tool))
       (token-budget (agent-state->token-budget st))
       (time-budget (agent-state->time-budget st)))
    (and (<= token-cost token-budget)
         (<= time-cost time-budget))))

;; Combined check: can we invoke this tool?
(define can-invoke-tool-p ((tool tool-spec-p) (st agent-state-p))
  :returns (result booleanp)
  (and (tool-permitted-p tool st)
       (tool-budget-sufficient-p tool st)))

;; Check if agent has an error
(define has-error-p ((st agent-state-p))
  :returns (result booleanp)
  (not (equal (error-kind-kind (agent-state->error-state st)) :none)))

;; Check if agent must respond (cannot continue)
(define must-respond-p ((st agent-state-p))
  :returns (result booleanp)
  (or (agent-state->done st)
      (has-error-p st)
      (>= (agent-state->step-counter st)
          (agent-state->max-steps st))
      (= (agent-state->token-budget st) 0)
      (= (agent-state->time-budget st) 0)))

;; Check if agent should continue (has budget and not satisfied)
(define should-continue-p ((st agent-state-p))
  :returns (result booleanp)
  (and (not (must-respond-p st))
       (< (agent-state->satisfaction st) *satisfaction-threshold*)))

;; Remaining steps (for termination measure)
(define remaining-steps ((st agent-state-p))
  :returns (n natp)
  (nfix (- (agent-state->max-steps st)
           (agent-state->step-counter st))))

;;;============================================================================
;;; Part 8: State Transition Functions
;;;============================================================================

;; Deduct tool cost from budgets
(define deduct-tool-cost ((tool tool-spec-p) (st agent-state-p))
  :returns (new-st agent-state-p)
  (b* ((token-cost (tool-spec->token-cost tool))
       (time-cost (tool-spec->time-cost tool))
       (old-tokens (agent-state->token-budget st))
       (old-time (agent-state->time-budget st)))
    (change-agent-state st
      :token-budget (nfix (- old-tokens token-cost))
      :time-budget (nfix (- old-time time-cost)))))

;; Increment step counter
(define increment-step ((st agent-state-p))
  :returns (new-st agent-state-p)
  (change-agent-state st
    :step-counter (1+ (agent-state->step-counter st))))

;; Update satisfaction level
(define update-satisfaction ((new-sat natp) (st agent-state-p))
  :returns (new-st agent-state-p)
  (change-agent-state st :satisfaction new-sat))

;; Mark agent as done
(define mark-done ((st agent-state-p))
  :returns (new-st agent-state-p)
  (change-agent-state st :done t))

;; Set error state
(define set-error ((err error-kind-p) (st agent-state-p))
  :returns (new-st agent-state-p)
  (change-agent-state st :error-state err))

;;;============================================================================
;;; Part 9: External Tool Oracle (Encapsulated)
;;;============================================================================

;; Abstract external tool calls - models MCP tools (Oxigraph, Qdrant, LLM)
;; ACL2 proves properties GIVEN ANY implementation satisfying these axioms
(encapsulate
  (((external-tool-call * *) => *))
  
  ;; Local witness function
  (local (defun external-tool-call (tool-name query)
           (declare (ignore tool-name query))
           (list 'success nil)))
  
  ;; Axiom: external calls return a list
  (defthm external-tool-call-returns-list
    (true-listp (external-tool-call tool-name query)))
  
  ;; Axiom: response has bounded length (resource safety)
  (defthm external-tool-call-bounded
    (< (len (external-tool-call tool-name query)) 10000)))

;;;============================================================================
;;; Part 10: ReAct Step Function
;;;============================================================================

;; Execute one ReAct step: process action and update state
(define react-step ((action agent-action-p) (tool tool-spec-p) (st agent-state-p))
  :returns (new-st agent-state-p)
  :guard (not (must-respond-p st))
  (b* ((st (increment-step st)))
    (agent-action-case action
      :tool-call
      (if (can-invoke-tool-p tool st)
          (deduct-tool-cost tool st)
        (set-error (error-kind-precondition-failed 
                     "Tool not permitted or insufficient budget")
                   st))
      :final-answer
      (mark-done st)
      :no-action
      st))
  :guard-hints (("Goal" :in-theory (enable must-respond-p))))

;;;============================================================================
;;; Part 11: Core Safety Theorems
;;;============================================================================

;; Theorem: can-invoke implies tool-permitted (permission safety)
(defthm permission-safety
  (implies (and (tool-spec-p tool)
                (agent-state-p st)
                (can-invoke-tool-p tool st))
           (tool-permitted-p tool st))
  :hints (("Goal" :in-theory (enable can-invoke-tool-p))))

;; Theorem: budgets remain non-negative after deduction
(defthm budget-bounds-after-deduct
  (implies (and (tool-spec-p tool)
                (agent-state-p st))
           (and (natp (agent-state->token-budget (deduct-tool-cost tool st)))
                (natp (agent-state->time-budget (deduct-tool-cost tool st)))))
  :hints (("Goal" :in-theory (enable deduct-tool-cost))))

;; Theorem: step counter increases after increment
(defthm step-increases-after-increment
  (implies (agent-state-p st)
           (> (agent-state->step-counter (increment-step st))
              (agent-state->step-counter st)))
  :hints (("Goal" :in-theory (enable increment-step))))

;; Theorem: reaching max-steps forces must-respond (termination bound)
(defthm termination-by-max-steps
  (implies (and (agent-state-p st)
                (>= (agent-state->step-counter st)
                    (agent-state->max-steps st)))
           (must-respond-p st))
  :hints (("Goal" :in-theory (enable must-respond-p))))

;; Theorem: agent state partitions into continue/respond/satisfied
(defthm continue-respond-partition
  (implies (agent-state-p st)
           (or (must-respond-p st)
               (should-continue-p st)
               (>= (agent-state->satisfaction st) *satisfaction-threshold*)))
  :hints (("Goal" :in-theory (enable must-respond-p should-continue-p)))
  :rule-classes nil)

;; Theorem: error state forces must-respond
(defthm error-state-forces-must-respond
  (implies (and (agent-state-p st)
                (has-error-p st))
           (must-respond-p st))
  :hints (("Goal" :in-theory (enable must-respond-p has-error-p))))

;; Theorem: remaining steps decreases (for termination proofs)
(defthm remaining-steps-decreases-after-increment
  (implies (and (agent-state-p st)
                (< (agent-state->step-counter st)
                   (agent-state->max-steps st)))
           (< (remaining-steps (increment-step st))
              (remaining-steps st)))
  :hints (("Goal" :in-theory (enable remaining-steps increment-step))))

;;;============================================================================
;;; Part 12: State Preservation Theorems
;;;============================================================================

;; All state transitions preserve agent-state-p (auto-proved by FTY)
;; Explicitly stated for documentation:

(defthm deduct-preserves-agent-state
  (implies (and (tool-spec-p tool) (agent-state-p st))
           (agent-state-p (deduct-tool-cost tool st))))

(defthm increment-preserves-agent-state
  (implies (agent-state-p st)
           (agent-state-p (increment-step st))))

(defthm update-satisfaction-preserves-agent-state
  (implies (and (natp new-sat) (agent-state-p st))
           (agent-state-p (update-satisfaction new-sat st))))

(defthm mark-done-preserves-agent-state
  (implies (agent-state-p st)
           (agent-state-p (mark-done st))))

(defthm set-error-preserves-agent-state
  (implies (and (error-kind-p err) (agent-state-p st))
           (agent-state-p (set-error err st))))

(defthm react-step-preserves-agent-state
  (implies (and (agent-action-p action)
                (tool-spec-p tool)
                (agent-state-p st))
           (agent-state-p (react-step action tool st))))
