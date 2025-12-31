; code-exec-demo.lisp - Demo of ACL2 Code Execution for Verified Agent
;
; This demonstrates the mini-swe-agent pattern adapted for ACL2:
; - Agent receives code from LLM in ```acl2 or ```lisp blocks
; - Code is extracted and executed via acl2s-compute
; - Results (success or error) are returned to conversation
; - Execute permission is enforced by verified agent
;
; Interactive Usage:
;   cd /workspaces/acl2-swf-experiments/experiments/agents
;   acl2
;   (ld "code-exec-demo.lisp")
;   :q
;   (run-demo)
;   (lp)

(in-package "ACL2")

;;;============================================================================
;;; Part 1: Load Dependencies
;;;============================================================================

(include-book "/workspaces/acl2-swf-experiments/experiments/agents/verified-agent")
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/code-exec"
              :ttags :all)

;;;============================================================================
;;; Part 2: Tool Specification for Code Execution
;;;============================================================================

;; Define tool spec for ACL2 code execution using verified-agent types
(defconst *acl2-compute-tool*
  (make-tool-spec
    :name 'acl2-compute
    :required-access 0        ; No file access needed
    :requires-execute t       ; REQUIRES execute permission!
    :token-cost 200           ; Budget for result output
    :time-cost 10))           ; 10 second typical

;;;============================================================================
;;; Part 3: Agent States - With and Without Execute Permission
;;;============================================================================

;; Agent WITH execute permission - can run code
(defconst *exec-enabled-state*
  (make-agent-state 
    :max-steps 20
    :token-budget 50000
    :time-budget 3600
    :file-access 1             ; Read access
    :execute-allowed t         ; CAN execute code
    :max-context-tokens 8000
    :satisfaction 0))

;; Agent WITHOUT execute permission - cannot run code
(defconst *exec-disabled-state*
  (make-agent-state 
    :max-steps 20
    :token-budget 50000
    :time-budget 3600
    :file-access 1             ; Read access
    :execute-allowed nil       ; CANNOT execute code
    :max-context-tokens 8000
    :satisfaction 0))

;;;============================================================================
;;; Part 4: Verify Permission Enforcement
;;;============================================================================

;; Check: enabled agent CAN invoke code execution tool
(defconst *can-exec-enabled*
  (prog2$ (cw "~%Agent with execute=t can invoke tool: ~x0~%"
              (can-invoke-tool-p *acl2-compute-tool* *exec-enabled-state*))
          (can-invoke-tool-p *acl2-compute-tool* *exec-enabled-state*)))

;; Check: disabled agent CANNOT invoke code execution tool
(defconst *can-exec-disabled*
  (prog2$ (cw "Agent with execute=nil can invoke tool: ~x0~%"
              (can-invoke-tool-p *acl2-compute-tool* *exec-disabled-state*))
          (can-invoke-tool-p *acl2-compute-tool* *exec-disabled-state*)))

;; The verified agent PROVES this property statically!
;; (See permission-safety theorem in verified-agent.lisp)

;;;============================================================================
;;; Part 5: Test Code Block Extraction
;;;============================================================================

;; Sample LLM response with code blocks
(defconst *sample-llm-response*
  "I'll help you with those calculations.

First, let's add some numbers:

```acl2
(+ 1 2 3 4 5)
```

Now let's work with lists:

```lisp
(append '(a b c) '(d e f))
```

And test a factorial:

```acl2
(defun fact (n)
  (if (zp n)
      1
    (* n (fact (1- n)))))
```

That covers the basics!")

;; Test extraction - this runs in logic mode
(defconst *extracted-blocks*
  (prog2$ (cw "~%=== Testing Code Block Extraction ===~%")
    (prog2$ (cw "Sample LLM response:~%~s0~%~%" *sample-llm-response*)
      (let ((blocks (extract-all-code-blocks *sample-llm-response*)))
        (prog2$ (cw "Found ~x0 code blocks~%" (len blocks))
          blocks)))))

;;;============================================================================
;;; Part 6: System Prompt for Code Execution Agent
;;;============================================================================

(defconst *code-agent-system-prompt*
  "You are an ACL2 theorem prover assistant with code execution capabilities.

You can execute ACL2 code to:
1. Evaluate expressions: (+ 1 2), (append '(a b) '(c d))
2. Test functions with examples
3. Explore ACL2 behavior

When you want to run ACL2 code, wrap it in code blocks like:

```acl2
(your-code-here)
```

or:

```lisp
(your-code-here)
```

The result will be returned to you showing either:
- Success: Result: <value>
- Error: Error message explaining what went wrong

Use the error messages to learn and fix your code.

TIPS:
- Quote literal lists: '(1 2 3) not (1 2 3)
- ACL2 is case-insensitive
- Guard violations mean type mismatches
- Use natp, integerp, etc. to check types")

;;;============================================================================
;;; Part 7: Demo Function (Run from Raw Lisp)
;;;============================================================================

#||
To run this demo:

1. Load the file:
   (ld "code-exec-demo.lisp")

2. Drop to raw Lisp:
   :q

3. Run the demo:
   (run-demo)

4. Return to ACL2:
   (lp)
||#

;; This function must be called from raw Lisp (after :q)
;; It demonstrates the full code execution flow
(defun run-demo ()
  "Run interactive demo of code execution. Call from raw Lisp."
  (format t "~%~%========================================~%")
  (format t "ACL2 Code Execution Demo~%")
  (format t "========================================~%~%")
  
  ;; Test 1: Simple arithmetic
  (format t "Test 1: Simple arithmetic~%")
  (format t "Code: (+ 1 2 3)~%")
  (format t "~A~%~%" (execute-code "(+ 1 2 3)"))
  
  ;; Test 2: List operations
  (format t "Test 2: List operations~%")
  (format t "Code: (append '(a b) '(c d))~%")
  (format t "~A~%~%" (execute-code "(append '(a b) '(c d))"))
  
  ;; Test 3: Error case - guard violation
  (format t "Test 3: Error case (guard violation)~%")
  (format t "Code: (car 5)~%")
  (format t "~A~%~%" (execute-code "(car 5)"))
  
  ;; Test 4: Error case - undefined function
  (format t "Test 4: Error case (undefined function)~%")
  (format t "Code: (my-undefined-function 42)~%")
  (format t "~A~%~%" (execute-code "(my-undefined-function 42)"))
  
  ;; Test 5: Extract and execute from LLM response
  (format t "Test 5: Extract code blocks from LLM response~%")
  (let* ((response "Let me calculate: ```acl2
(* 6 7)
``` That should give us 42.")
         (blocks (extract-all-code-blocks response)))
    (format t "Response: ~S~%" response)
    (format t "Extracted blocks: ~S~%" blocks)
    (when blocks
      (format t "Executing first block:~%")
      (format t "~A~%" (execute-code (car blocks)))))
  
  ;; Test 6: Both ```acl2 and ```lisp fences
  (format t "~%Test 6: Both fence types~%")
  (let* ((response "
```acl2
(+ 10 20)
```

```lisp
(length '(a b c d e))
```
")
         (results (execute-code-blocks response)))
    (format t "Response with both fence types:~%")
    (format t "Results:~%")
    (dolist (r results)
      (format t "  Code: ~S~%" (car r))
      (format t "  ~A~%~%" (cdr r))))
  
  (format t "========================================~%")
  (format t "Demo Complete!~%")
  (format t "========================================~%")
  t)

;;;============================================================================
;;; Part 8: Permission Safety Verification
;;;============================================================================

;; The key theorem from verified-agent.lisp guarantees:
;; If can-invoke-tool-p returns T, permission requirements are satisfied
;;
;; For *acl2-compute-tool*: requires-execute = T
;; So can-invoke-tool-p only succeeds when execute-allowed = T

(defconst *permission-check*
  (prog2$ (cw "~%=== Permission Safety Verification ===~%")
    (prog2$ (cw "Tool requires execute: ~x0~%" 
                (tool-spec->requires-execute *acl2-compute-tool*))
      (prog2$ (cw "Enabled agent: can-invoke = ~x0~%"
                  (can-invoke-tool-p *acl2-compute-tool* *exec-enabled-state*))
        (prog2$ (cw "Disabled agent: can-invoke = ~x0~%"
                    (can-invoke-tool-p *acl2-compute-tool* *exec-disabled-state*))
          (cw "Permission safety PROVEN by ACL2 theorem!~%"))))))

;;;============================================================================
;;; Part 9: Summary
;;;============================================================================

(defconst *demo-loaded*
  (prog2$ (cw "~%========================================~%")
    (prog2$ (cw "Code Execution Demo Loaded~%")
      (prog2$ (cw "========================================~%")
        (prog2$ (cw "~%To run the interactive demo:~%")
          (prog2$ (cw "  :q~%")
            (prog2$ (cw "  (run-demo)~%")
              (prog2$ (cw "  (lp)~%~%")
                t))))))))
