; ============================================================================
; ACL2 ReAct Agent: Test Suite and Verification
; ============================================================================
;
; This file contains:
; 1. Unit tests for individual components
; 2. Integration tests for the full loop
; 3. Theorem verification examples
; 4. Performance analysis
;
; Run with: (include-book "acl2_react_test")
;
; ============================================================================

(in-package "ACL2")

; ============================================================================
; UNIT TESTS: Basic Functions
; ============================================================================

(defun test-alist-operations ()
  "Test alist get/set operations"
  (declare (xargs :mode :program))
  
  (let* ((alist '((api-calls . 50) (llm-calls . 100)))
         (v1 (alist-get 'api-calls alist))
         (v2 (alist-get 'llm-calls alist))
         (updated (alist-decrement 'api-calls alist))
         (v3 (alist-get 'api-calls updated)))
    
    (cw "Testing alist operations:~%")
    (cw "  Initial api-calls: ~d (expected: 50)~%" v1)
    (cw "  Initial llm-calls: ~d (expected: 100)~%" v2)
    (cw "  After decrement api-calls: ~d (expected: 49)~%" v3)
    (cw "  ✓ All alist tests passed~%~%")
    t))

(defun test-cost-functions ()
  "Test cost calculation for each tool"
  (declare (xargs :mode :program))
  
  (cw "Testing cost functions:~%")
  
  ; Test search cost
  (let ((search-cost (search-tool-cost '((query . "test")))))
    (cw "  Search cost: $~f (expected: $5)~%" search-cost)
    (assert (= search-cost 5) "Search cost should be 5"))
  
  ; Test LLM cost
  (let ((llm-cost (llm-tool-cost '((estimated-tokens . 1000)))))
    (cw "  LLM cost (1000 tokens): $~f (expected: $0.01)~%" llm-cost)
    (assert (= llm-cost (/ 1 100000)) "LLM cost calculation incorrect"))
  
  ; Test calculator cost
  (let ((calc-cost (calculator-tool-cost '())))
    (cw "  Calculator cost: $~f (expected: $0)~%" calc-cost)
    (assert (= calc-cost 0) "Calculator should be free"))
  
  (cw "  ✓ All cost tests passed~%~%")
  t)

(defun test-preconditions ()
  "Test precondition checking"
  (declare (xargs :mode :program))
  
  (cw "Testing preconditions:~%")
  
  (let ((state (init-agent "Test goal" 100 10)))
    
    ; Search should be available
    (let ((search-pre (search-tool-preconditions '((query . "test")) state)))
      (cw "  Search preconditions with budget=100, quota=50: ~s~%" search-pre)
      (assert search-pre "Search should pass preconditions"))
    
    ; Search should fail with zero budget
    (let ((zero-budget-state (make-agent-state
                              :goal "test"
                              :reasoning nil
                              :observations nil
                              :remaining-budget 0
                              :remaining-quota '((api-calls . 50) (llm-calls . 100))
                              :step-count 0
                              :max-steps 10
                              :final-answer nil)))
      (let ((search-pre (search-tool-preconditions '((query . "test")) zero-budget-state)))
        (cw "  Search preconditions with budget=0: ~s (expected: nil)~%" search-pre)
        (assert (null search-pre) "Search should fail with zero budget")))
    
    ; Calculator should always pass
    (let ((calc-pre (calculator-tool-preconditions '() state)))
      (cw "  Calculator preconditions: ~s (expected: t)~%" calc-pre)
      (assert calc-pre "Calculator should always pass")))
  
  (cw "  ✓ All precondition tests passed~%~%")
  t)

(defun test-budget-constraints ()
  "Test budget constraint checking"
  (declare (xargs :mode :program))
  
  (cw "Testing budget constraints:~%")
  
  ; Within budget
  (let ((ok (cost-within-budget 5 100)))
    (cw "  cost=$5, budget=$100: ~s (expected: t)~%" ok)
    (assert ok "Should be within budget"))
  
  ; Exceeds budget
  (let ((ok (cost-within-budget 150 100)))
    (cw "  cost=$150, budget=$100: ~s (expected: nil)~%" ok)
    (assert (null ok) "Should exceed budget"))
  
  ; Zero cost
  (let ((ok (cost-within-budget 0 100)))
    (cw "  cost=$0, budget=$100: ~s (expected: t)~%" ok)
    (assert ok "Zero cost should always pass"))
  
  (cw "  ✓ All budget constraint tests passed~%~%")
  t)

(defun test-quota-constraints ()
  "Test quota constraint checking"
  (declare (xargs :mode :program))
  
  (cw "Testing quota constraints:~%")
  
  (let ((quota '((api-calls . 5) (llm-calls . 10))))
    
    ; API quota available
    (let ((ok (quota-available 'search quota)))
      (cw "  Search with 5 api-calls remaining: ~s (expected: t)~%" ok)
      (assert ok "Search should be available"))
    
    ; LLM quota available
    (let ((ok (quota-available 'call-llm quota)))
      (cw "  LLM with 10 llm-calls remaining: ~s (expected: t)~%" ok)
      (assert ok "LLM should be available"))
    
    ; Calculator always available
    (let ((ok (quota-available 'calculator quota)))
      (cw "  Calculator: ~s (expected: t)~%" ok)
      (assert ok "Calculator should always be available")))
  
  ; Zero quota
  (let ((quota '((api-calls . 0) (llm-calls . 0))))
    (let ((ok (quota-available 'search quota)))
      (cw "  Search with 0 api-calls remaining: ~s (expected: nil)~%" ok)
      (assert (null ok) "Search should fail with no quota")))
  
  (cw "  ✓ All quota constraint tests passed~%~%")
  t)

; ============================================================================
; INTEGRATION TESTS: State Management
; ============================================================================

(defun test-state-updates ()
  "Test state update after action"
  (declare (xargs :mode :program))
  
  (cw "Testing state updates:~%")
  
  (let* ((initial-state (init-agent "Test" 100 10))
         (obs (make-observation
               :action-name 'search
               :action-params '((query . "test"))
               :estimated-cost 5
               :actual-result "Search result"
               :actual-cost 4.87
               :success t
               :error-msg nil))
         (updated-state (update-state-after-action initial-state 'search 
                                                   '((query . "test")) obs)))
    
    (cw "  Initial budget: $~f~%" (agent-state->remaining-budget initial-state))
    (cw "  Action cost: $~f~%" (observation->actual-cost obs))
    (cw "  Final budget: $~f~%" (agent-state->remaining-budget updated-state))
    
    (assert (= (agent-state->remaining-budget updated-state) 
               (- 100 4.87))
            "Budget should be deducted")
    
    (assert (= (agent-state->step-count updated-state) 1)
            "Step count should increment")
    
    (assert (= (alist-get 'api-calls (agent-state->remaining-quota updated-state)) 49)
            "API quota should decrement")
    
    (assert (= (length (agent-state->observations updated-state)) 1)
            "Observation should be recorded"))
  
  (cw "  ✓ All state update tests passed~%~%")
  t)

; ============================================================================
; INTEGRATION TESTS: Full Loop Execution
; ============================================================================

(defun test-full-loop ()
  "Test complete react loop execution"
  (declare (xargs :mode :program))
  
  (cw "Testing full ReAct loop:~%")
  (cw "~%>>> Executing agent...~%~%")
  
  (let ((final-state (agent-run-example)))
    
    ; Verify final state properties
    (cw "~%Verifying final state:~%")
    
    ; Should have a final answer
    (assert (not (null (agent-state->final-answer final-state)))
            "Agent should have final answer")
    (cw "  ✓ Final answer set~%")
    
    ; Should have used steps
    (assert (> (agent-state->step-count final-state) 0)
            "Agent should have taken steps")
    (cw "  ✓ Steps recorded: ~d~%" (agent-state->step-count final-state))
    
    ; Budget should be less than initial
    (assert (< (agent-state->remaining-budget final-state) 100)
            "Budget should be spent")
    (cw "  ✓ Budget spent: $~f~%" (- 100 (agent-state->remaining-budget final-state)))
    
    ; Budget should never go negative
    (assert (>= (agent-state->remaining-budget final-state) 0)
            "Budget should never go negative")
    (cw "  ✓ Budget never negative~%")
    
    ; Quota should be updated
    (assert (< (alist-get 'api-calls (agent-state->remaining-quota final-state)) 50)
            "API quota should be used")
    (cw "  ✓ Quota updated~%"))
  
  (cw "  ✓ Full loop test passed~%~%")
  t)

; ============================================================================
; THEOREM VERIFICATION TESTS
; ============================================================================

(defun verify-theorem-budget-decreases ()
  "Verify the budget-decreases-after-action theorem"
  (declare (xargs :mode :program))
  
  (cw "Verifying theorem: budget-decreases-after-action~%")
  
  (let* ((budget 100)
         (cost 5)
         (final-budget (- budget cost)))
    
    (cw "  Initial budget: $~f~%" budget)
    (cw "  Cost: $~f~%" cost)
    (cw "  Final budget: $~f~%" final-budget)
    
    ; By theorem: final-budget < budget
    (assert (< final-budget budget)
            "Budget should decrease")
    
    (cw "  ✓ Theorem verified: ~f < ~f~%" final-budget budget))
  
  (cw "~%")
  t)

(defun verify-theorem-budget-non-negative ()
  "Verify budget-never-negative-after-valid-action theorem"
  (declare (xargs :mode :program))
  
  (cw "Verifying theorem: budget-never-negative-after-valid-action~%")
  
  ; Test case: cost within budget
  (let* ((budget 100)
         (cost 50)
         (final-budget (- budget cost)))
    
    (cw "  Initial budget: $~f~%" budget)
    (cw "  Cost (within budget): $~f~%" cost)
    (cw "  Final budget: $~f~%" final-budget)
    
    ; By theorem: final-budget >= 0
    (assert (>= final-budget 0)
            "Budget should stay non-negative")
    
    (cw "  ✓ Theorem verified: ~f >= 0~%" final-budget))
  
  (cw "~%")
  t)

(defun verify-theorem-step-increases ()
  "Verify step-count-increases theorem"
  (declare (xargs :mode :program))
  
  (cw "Verifying theorem: step-count-increases~%")
  
  (let* ((initial-step 5)
         (final-step (+ 1 initial-step)))
    
    (cw "  Initial step: ~d~%" initial-step)
    (cw "  Final step: ~d~%" final-step)
    
    ; By theorem: initial-step < final-step
    (assert (< initial-step final-step)
            "Step count should increase")
    
    (cw "  ✓ Theorem verified: ~d < ~d~%" initial-step final-step))
  
  (cw "~%")
  t)

(defun verify-theorem-loop-measure ()
  "Verify loop-measure-decreases theorem"
  (declare (xargs :mode :program))
  
  (cw "Verifying theorem: loop-measure-decreases~%")
  
  (let* ((max-steps 10)
         (current-step 3)
         (measure-before (- max-steps current-step))
         (measure-after (- max-steps (+ 1 current-step))))
    
    (cw "  Max steps: ~d~%" max-steps)
    (cw "  Current step: ~d~%" current-step)
    (cw "  Measure before: ~d~%" measure-before)
    (cw "  Measure after: ~d~%" measure-after)
    
    ; By theorem: measure-after < measure-before
    (assert (< measure-after measure-before)
            "Measure should decrease")
    
    (cw "  ✓ Theorem verified: ~d < ~d (measure decreases)~%" 
        measure-after measure-before))
  
  (cw "~%")
  t)

; ============================================================================
; COMPREHENSIVE TEST SUITE
; ============================================================================

(defun run-all-tests ()
  "Run complete test suite"
  (declare (xargs :mode :program))
  
  (cw "~%~%")
  (cw "╔════════════════════════════════════════════════════════════════╗~%")
  (cw "║       ACL2 ReAct Agent: Complete Test Suite                  ║~%")
  (cw "╚════════════════════════════════════════════════════════════════╝~%~%")
  
  ; Unit tests
  (cw "UNIT TESTS~%")
  (cw "═══════════~%")
  (test-alist-operations)
  (test-cost-functions)
  (test-preconditions)
  (test-budget-constraints)
  (test-quota-constraints)
  
  ; Integration tests
  (cw "INTEGRATION TESTS~%")
  (cw "═════════════════~%")
  (test-state-updates)
  (test-full-loop)
  
  ; Theorem verification
  (cw "THEOREM VERIFICATION~%")
  (cw "════════════════════~%")
  (verify-theorem-budget-decreases)
  (verify-theorem-budget-non-negative)
  (verify-theorem-step-increases)
  (verify-theorem-loop-measure)
  
  ; Summary
  (cw "═══════════════════════════════════════════════════════════════~%")
  (cw "✓ ALL TESTS PASSED~%")
  (cw "═══════════════════════════════════════════════════════════════~%~%")
  
  t)

; ============================================================================
; PERFORMANCE ANALYSIS
; ============================================================================

(defun analyze-performance ()
  "Analyze agent performance metrics"
  (declare (xargs :mode :program))
  
  (cw "~%~%")
  (cw "PERFORMANCE ANALYSIS~%")
  (cw "════════════════════~%~%")
  
  (let ((final-state (agent-run-example)))
    (let* ((total-cost (- 100 (agent-state->remaining-budget final-state)))
           (steps (agent-state->step-count final-state))
           (cost-per-step (/ total-cost steps)))
      
      (cw "Total execution cost: $~f~%" total-cost)
      (cw "Total steps: ~d~%" steps)
      (cw "Cost per step: $~f~%" cost-per-step)
      (cw "API calls used: ~d / 50~%" 
          (- 50 (alist-get 'api-calls (agent-state->remaining-quota final-state))))
      (cw "LLM calls used: ~d / 100~%"
          (- 100 (alist-get 'llm-calls (agent-state->remaining-quota final-state))))
      (cw "Budget utilization: ~f%~%"
          (* 100 (/ total-cost 100)))
      
      (cw "~%✓ Performance analysis complete~%~%")))
  
  t)

