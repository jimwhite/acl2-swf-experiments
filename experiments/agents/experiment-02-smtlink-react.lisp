; Verified ReAct Agent with SMTLink Z3 Code Generation
;
; This experiment evolves experiment-01 to use ACL2 SMTLink for:
; 1. FTY defprod types for agent-state and tool-spec
; 2. SMTLink proves theorems via Z3
; 3. Generated Z3 Python code is preserved for runtime enforcement
;
; The key insight: SMTLink translates ACL2 constraints to Z3 Python code.
; We capture that code and use it at runtime in LangGraph.

(in-package "ACL2")

;;; ==========================================================================
;;; SMTLink Setup
;;; ==========================================================================

(include-book "projects/smtlink/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

; Enable tshell for running Z3
(value-triple (tshell-ensure))

; Add SMTLink computed hints
(add-default-hints '((SMT::SMT-computed-hint clause)))

;;; ==========================================================================
;;; Part 1: FTY Types for Agent State and Tool Spec
;;; ==========================================================================

;; Agent state as FTY product type
;; Using integerp for SMTLink compatibility (maps to Z3 Int)
(fty::defprod agent-state
  ((iteration      integerp :default 0)
   (max-iterations integerp :default 10)
   (token-budget   integerp :default 10000)
   (cost-budget    integerp :default 1000)   ; millicents
   (time-budget    integerp :default 60000)  ; ms
   (file-access    integerp :default 0)      ; 0=none, 1=read, 2=read-write
   (exec-allowed   booleanp :default nil)
   (satisfaction   integerp :default 0)      ; 0-100 (percentage)
   (done           booleanp :default nil))
  :parents (experiment-02))

;; Tool spec as FTY product type
(fty::defprod tool-spec
  ((required-access integerp :default 0)
   (requires-exec   booleanp :default nil)
   (base-cost       integerp :default 0)
   (time-estimate   integerp :default 0)
   (token-estimate  integerp :default 0))
  :parents (experiment-02))

;;; ==========================================================================
;;; Part 2: Constants for Thresholds
;;; ==========================================================================

(defconst *access-none* 0)
(defconst *access-read* 1)
(defconst *access-read-write* 2)

(defconst *min-llm-tokens* 100)
(defconst *min-iteration-cost* 10)
(defconst *min-iteration-time* 1000)
(defconst *satisfaction-threshold* 90)  ; percentage

;;; ==========================================================================
;;; Part 3: Permission Checking (using integers for SMTLink)
;;; ==========================================================================

;; Check if granted access is sufficient
;; Note: We access FTY fields directly - they're already integers
(define access-sufficient-p ((required integerp) (granted integerp))
  :returns (ok booleanp)
  (<= required granted))

;; Full permission check: file access + execute
(define tool-permitted-p ((tool tool-spec-p) (st agent-state-p))
  :returns (ok booleanp)
  (b* ((required-access (tool-spec->required-access tool))
       (requires-exec (tool-spec->requires-exec tool))
       (granted-access (agent-state->file-access st))
       (exec-allowed (agent-state->exec-allowed st)))
    (and (access-sufficient-p required-access granted-access)
         (implies requires-exec exec-allowed))))

;;; ==========================================================================
;;; Part 4: Budget Checking
;;; ==========================================================================

;; Check if budget is sufficient for a tool call
(define tool-budget-sufficient-p ((tool tool-spec-p) (st agent-state-p))
  :returns (ok booleanp)
  (b* ((tool-cost (tool-spec->base-cost tool))
       (tool-time (tool-spec->time-estimate tool))
       (tool-tokens (tool-spec->token-estimate tool))
       (budget-cost (agent-state->cost-budget st))
       (budget-time (agent-state->time-budget st))
       (budget-tokens (agent-state->token-budget st)))
    (and (<= tool-cost budget-cost)
         (<= tool-time budget-time)
         (<= tool-tokens budget-tokens))))

;; Can we invoke this tool?
(define can-invoke-tool-p ((tool tool-spec-p) (st agent-state-p))
  :returns (ok booleanp)
  (and (tool-permitted-p tool st)
       (tool-budget-sufficient-p tool st)))

;;; ==========================================================================
;;; Part 5: Continue vs Respond Decision
;;; ==========================================================================

;; Must respond: out of budget or done
(define must-respond-p ((st agent-state-p))
  :returns (must booleanp)
  (b* ((done (agent-state->done st))
       (iter (agent-state->iteration st))
       (max-iter (agent-state->max-iterations st))
       (tokens (agent-state->token-budget st))
       (cost (agent-state->cost-budget st))
       (time-ms (agent-state->time-budget st)))
    (or done
        (>= iter max-iter)
        (< tokens *min-llm-tokens*)
        (< cost *min-iteration-cost*)
        (< time-ms *min-iteration-time*))))

;; Should continue: has budget and below satisfaction threshold
(define should-continue-p ((st agent-state-p))
  :returns (cont booleanp)
  (b* ((sat (agent-state->satisfaction st)))
    (and (not (must-respond-p st))
         (< sat *satisfaction-threshold*))))

;;; ==========================================================================
;;; Part 6: State Update Functions
;;; ==========================================================================

;; Deduct tool costs from state
;; Note: Use (max 0 ...) to ensure non-negative, avoiding ifix
(define deduct-tool-cost ((tool tool-spec-p) (st agent-state-p))
  :returns (new-st agent-state-p)
  (b* ((tool-cost (tool-spec->base-cost tool))
       (tool-time (tool-spec->time-estimate tool))
       (tool-tokens (tool-spec->token-estimate tool))
       (budget-cost (agent-state->cost-budget st))
       (budget-time (agent-state->time-budget st))
       (budget-tokens (agent-state->token-budget st))
       ;; Use max 0 to ensure non-negative (max is supported by SMTLink)
       (new-cost (max 0 (- budget-cost tool-cost)))
       (new-time (max 0 (- budget-time tool-time)))
       (new-tokens (max 0 (- budget-tokens tool-tokens))))
    (change-agent-state st
                        :cost-budget new-cost
                        :time-budget new-time
                        :token-budget new-tokens)))

;; Increment iteration
(define increment-iteration ((st agent-state-p))
  :returns (new-st agent-state-p)
  (change-agent-state st
                      :iteration (1+ (agent-state->iteration st))))

;; Update satisfaction score
(define update-satisfaction ((new-sat integerp) (st agent-state-p))
  :returns (new-st agent-state-p)
  ;; Clamp to 0-100 using max/min (SMTLink-compatible)
  (b* ((clamped (max 0 (min 100 new-sat))))
    (change-agent-state st :satisfaction clamped)))

;; Mark done
(define mark-done ((st agent-state-p))
  :returns (new-st agent-state-p)
  (change-agent-state st :done t))

;;; ==========================================================================
;;; Part 7: SMTLink Theorems - Z3 Proves These  
;;; ==========================================================================
;;;
;;; These theorems use SMTLink to generate Z3 Python code.
;;; We configure SMTLink to preserve the generated file.
;;;
;;; Key: SMTLink treats FTY recognizers (agent-state-p, tool-spec-p) as type
;;; declarations, so we don't add explicit integerp hypotheses.

;; Theorem 1: Permission safety (can-invoke implies permitted)
;; This is proven by Z3 via SMTLink
(defthm permission-safety-smt
  (implies (and (tool-spec-p tool)
                (agent-state-p st)
                (can-invoke-tool-p tool st))
           (tool-permitted-p tool st))
  :hints (("Goal"
           :smtlink
           (:fty (tool-spec agent-state)
            :smt-fname "react_permission_safety.py"
            :rm-file nil))))

;; Theorem 2: Budget bounds - deduction keeps budgets non-negative
;; Using >= 0 constraints as these are within the FTY-understood types
(defthm budget-bounds-smt
  (implies (and (tool-spec-p tool)
                (agent-state-p st)
                (>= (agent-state->cost-budget st) 0)
                (>= (agent-state->time-budget st) 0)
                (>= (agent-state->token-budget st) 0))
           (and (>= (agent-state->cost-budget (deduct-tool-cost tool st)) 0)
                (>= (agent-state->time-budget (deduct-tool-cost tool st)) 0)
                (>= (agent-state->token-budget (deduct-tool-cost tool st)) 0)))
  :hints (("Goal"
           :smtlink
           (:fty (tool-spec agent-state)
            :smt-fname "react_budget_bounds.py"
            :rm-file nil))))

;; Theorem 3: Iteration bound guarantees termination
(defthm termination-bound-smt
  (implies (and (agent-state-p st)
                (>= (agent-state->iteration st) (agent-state->max-iterations st)))
           (must-respond-p st))
  :hints (("Goal"
           :smtlink
           (:fty (agent-state)
            :smt-fname "react_termination.py"
            :rm-file nil))))

;; Theorem 4: Continue/respond are mutually exclusive and exhaustive
;; (when satisfaction is properly bounded)
(defthm continue-respond-partition-smt
  (implies (and (agent-state-p st)
                (>= (agent-state->satisfaction st) 0)
                (<= (agent-state->satisfaction st) 100))
           (or (must-respond-p st)
               (should-continue-p st)
               (>= (agent-state->satisfaction st) *satisfaction-threshold*)))
  :hints (("Goal"
           :smtlink
           (:fty (agent-state)
            :smt-fname "react_partition.py"
            :rm-file nil))))

;;; ==========================================================================
;;; Part 8: Pure ACL2 Theorems (no SMTLink)
;;; ==========================================================================

;; These theorems are proven by ACL2 alone, providing additional guarantees

(defthm iteration-increases
  (implies (agent-state-p st)
           (< (agent-state->iteration st)
              (agent-state->iteration (increment-iteration st))))
  :hints (("Goal" :in-theory (enable increment-iteration))))

(defthm deduct-preserves-agent-state
  (implies (and (tool-spec-p tool)
                (agent-state-p st))
           (agent-state-p (deduct-tool-cost tool st)))
  :hints (("Goal" :in-theory (enable deduct-tool-cost))))

(defthm update-satisfaction-preserves-agent-state
  (implies (and (integerp new-sat)
                (agent-state-p st))
           (agent-state-p (update-satisfaction new-sat st)))
  :hints (("Goal" :in-theory (enable update-satisfaction))))

(defthm mark-done-preserves-agent-state
  (implies (agent-state-p st)
           (agent-state-p (mark-done st)))
  :hints (("Goal" :in-theory (enable mark-done))))

(defthm increment-preserves-agent-state
  (implies (agent-state-p st)
           (agent-state-p (increment-iteration st)))
  :hints (("Goal" :in-theory (enable increment-iteration))))

;;; ==========================================================================
;;; End of Experiment 02
;;; ==========================================================================
;;;
;;; After certification, check /tmp/py_file/ for generated Z3 Python files:
;;; - react_permission_safety.py
;;; - react_budget_bounds.py  
;;; - react_termination.py
;;; - react_partition.py
;;;
;;; These files contain the Z3 constraints that can be adapted for runtime
;;; enforcement in the LangGraph agent.
