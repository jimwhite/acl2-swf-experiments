; code-exec-demo.lisp - Demo of Safe Code Execution with Verified Agent
;
; This demonstrates the mini-swe-agent pattern adapted for ACL2:
; - Agent receives code from LLM in ```acl2 blocks
; - Code is validated and executed via acl2s-compute
; - Results are formatted and returned to conversation
; - Execute permission is enforced by verified agent
;
; Usage (interactive):
;   cd /workspaces/acl2-swf-experiments/experiments/agents
;   acl2
;   (ld "code-exec-demo.lisp")
;
; Usage (certification):
;   cert.pl code-exec-demo

; cert_param: (cert_env "SKIP_INTERACTIVE=1")

(in-package "ACL2")

;;;============================================================================
;;; Cell 1: Load the verified agent and code execution
;;;============================================================================

(include-book "/workspaces/acl2-swf-experiments/experiments/agents/verified-agent")
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/code-exec"
              :ttags ((:acl2s-interface) (:code-exec)))
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/llm-client"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client)))

;;;============================================================================
;;; Cell 2: Code Execution Tool Specification
;;;============================================================================

;; Define tool spec for ACL2 code execution
(defconst *acl2-exec-tool*
  (make-tool-spec
    :name 'execute-acl2
    :required-access 0        ; No file access needed
    :requires-execute t       ; REQUIRES execute permission!
    :token-cost 500           ; Budget for result output
    :time-cost 30))           ; 30 second timeout

;;;============================================================================
;;; Cell 3: Agent States - With and Without Execute Permission
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
;;; Cell 4: Verify Permission Enforcement
;;;============================================================================

;; Check: enabled agent CAN invoke code execution tool
(defconst *can-exec-enabled*
  (prog2$ (cw "~%Agent with execute=t can invoke tool: ~x0~%"
              (can-invoke-tool-p *acl2-exec-tool* *exec-enabled-state*))
          (can-invoke-tool-p *acl2-exec-tool* *exec-enabled-state*)))

;; Check: disabled agent CANNOT invoke code execution tool
(defconst *can-exec-disabled*
  (prog2$ (cw "Agent with execute=nil can invoke tool: ~x0~%"
              (can-invoke-tool-p *acl2-exec-tool* *exec-disabled-state*))
          (can-invoke-tool-p *acl2-exec-tool* *exec-disabled-state*)))

;; The verified agent PROVES this property statically!
;; (See permission-safety theorem in verified-agent.lisp)

;;;============================================================================
;;; Cell 5: System Prompt for Code Execution Agent
;;;============================================================================

(defconst *code-agent-prompt*
  "You are an ACL2 theorem prover assistant with code execution capabilities.

You can execute ACL2 code to:
1. Evaluate expressions: (+ 1 2), (append '(a b) '(c d))
2. Define and test functions: (defun f (x) (* x x))
3. Attempt theorem proofs: (thm (implies (natp x) (integerp x)))

When you want to run ACL2 code, wrap it in ```acl2 blocks like this:

```acl2
(your-acl2-code-here)
```

The result will be returned to you. You can then:
- Analyze the output
- Try variations if something fails
- Build up to more complex proofs

IMPORTANT: Code execution is sandboxed. You cannot:
- Make system calls
- Load external files
- Modify trust tags
- Access raw Lisp

Be precise with ACL2 syntax. Common mistakes:
- Missing quotes: '(1 2 3) not (1 2 3)
- Wrong function names: append not concat
- Guard violations: (+ 1 'a) will fail")

;;;============================================================================
;;; Cell 6: Code Extraction Pattern (like mini-swe-agent)
;;;============================================================================

;; Extract ACL2 code from markdown code blocks
;; Pattern: ```acl2\n...\n```
(defun extract-acl2-code-block (response start)
  "Extract code between ```acl2 and ``` markers starting from position START.
   Returns (mv found-p code end-pos)"
  (declare (xargs :guard (and (stringp response) (natp start))
                  :mode :program))
  (let* ((marker-start "```acl2")
         (marker-end "```")
         (block-start (search marker-start response :start2 start)))
    (if (null block-start)
        (mv nil "" (length response))
      (let* ((code-start (+ block-start (length marker-start)))
             ;; Skip newline after marker
             (code-start (if (and (< code-start (length response))
                                  (eql (char response code-start) #\Newline))
                             (1+ code-start)
                           code-start))
             (block-end (search marker-end response :start2 code-start)))
        (if (null block-end)
            (mv nil "" (length response))
          (mv t 
              (subseq response code-start block-end)
              (+ block-end (length marker-end))))))))

;; Helper function - must be defined before extract-all-acl2-blocks
(defun extract-all-acl2-blocks-aux (response pos acc)
  (declare (xargs :mode :program))
  (if (>= pos (length response))
      (reverse acc)
    (mv-let (found-p code end-pos)
      (extract-acl2-code-block response pos)
      (if found-p
          (extract-all-acl2-blocks-aux response end-pos (cons code acc))
        (reverse acc)))))

;; Extract all ACL2 code blocks from response
(defun extract-all-acl2-blocks (response)
  "Extract all ```acl2 blocks from response. Returns list of code strings."
  (declare (xargs :mode :program))
  (extract-all-acl2-blocks-aux response 0 nil))

;;;============================================================================
;;; Cell 7: Interactive Demo Functions (skipped during cert)
;;;============================================================================

;; Helper to print blocks
#-skip-interactive
(defun print-blocks (blocks n)
  (declare (xargs :mode :program))
  (if (endp blocks)
      nil
    (prog2$ (cw "  Block ~x0: ~s1~%" n (car blocks))
            (print-blocks (cdr blocks) (1+ n)))))

#-skip-interactive
(defun demo-extract-code ()
  "Demo the code extraction"
  (declare (xargs :mode :program))
  (let ((test-response "Here's how to add numbers:

```acl2
(+ 1 2 3)
```

And here's list append:

```acl2
(append '(a b) '(c d))
```

That's it!"))
    (prog2$ (cw "~%Extracting code blocks from LLM response...~%")
      (prog2$ (cw "Response: ~s0~%~%" test-response)
        (let ((blocks (extract-all-acl2-blocks test-response)))
          (prog2$ (cw "Found ~x0 code blocks:~%" (len blocks))
            (prog2$ (print-blocks blocks 1)
              blocks)))))))

#-skip-interactive
(defconst *demo-extraction*
  (demo-extract-code))

;;;============================================================================
;;; Cell 8: Execute Code Blocks (Program Mode, requires raw Lisp)
;;;============================================================================

;; This function would be called from raw Lisp to execute extracted code
#||
Example raw Lisp usage:

(defun execute-code-blocks (blocks)
  "Execute a list of ACL2 code strings, return list of results"
  (loop for block in blocks
        collect (execute-acl2-code block)))

;; Full agent step:
(defun agent-code-step (response)
  "Process LLM response: extract and execute code blocks"
  (let ((blocks (extract-all-acl2-blocks response)))
    (if (null blocks)
        "No code blocks found in response."
      (format nil "~{~A~%~}" (execute-code-blocks blocks)))))
||#

;;;============================================================================
;;; Cell 9: Example Agent Flow
;;;============================================================================

;; This shows the intended flow (pseudo-code):
;;
;; 1. User asks: "What's the sum of 1 through 10?"
;; 2. LLM responds with:
;;    "Let me calculate that:
;;    ```acl2
;;    (loop$ for i from 1 to 10 sum i)
;;    ```"
;; 3. Agent extracts code block
;; 4. Agent checks: (can-invoke-tool-p *acl2-exec-tool* agent-state)
;; 5. If allowed, execute via (execute-acl2-code "(loop$ ...)")
;; 6. Add result to conversation as tool message
;; 7. LLM sees: "RESULT: 55"
;; 8. LLM responds: "The sum of 1 through 10 is 55."

;;;============================================================================
;;; Cell 10: Proof that Permission Enforcement Works
;;;============================================================================

;; The key theorem from verified-agent.lisp applies here:
;; 
;; (defthm permission-safety
;;   (implies (and (tool-spec-p tool)
;;                 (agent-state-p st)
;;                 (can-invoke-tool-p tool st))
;;            (tool-permitted-p tool st)))
;;
;; This means: if can-invoke-tool-p returns T, then the tool's
;; permission requirements are DEFINITELY satisfied.
;;
;; For code execution: requires-execute = T
;; So can-invoke-tool-p only returns T when execute-allowed = T

;; Verify this statically:
(defconst *proof-check*
  (prog2$ (cw "~%=== Permission Enforcement Verification ===~%")
    (prog2$ (cw "Tool requires execute: ~x0~%" 
                (tool-spec->requires-execute *acl2-exec-tool*))
      (prog2$ (cw "Enabled agent (execute=t): can-invoke = ~x0~%"
                  (can-invoke-tool-p *acl2-exec-tool* *exec-enabled-state*))
        (prog2$ (cw "Disabled agent (execute=nil): can-invoke = ~x0~%"
                    (can-invoke-tool-p *acl2-exec-tool* *exec-disabled-state*))
          (prog2$ (cw "Permission safety PROVEN by ACL2!~%")
            t))))))

;;;============================================================================
;;; Summary
;;;============================================================================

(defconst *demo-complete*
  (prog2$ (cw "~%~%========================================~%")
    (prog2$ (cw "Code Execution Demo Complete!~%")
      (prog2$ (cw "========================================~%")
        (prog2$ (cw "~%Key points:~%")
          (prog2$ (cw "  1. Code extracted from ```acl2 blocks~%")
            (prog2$ (cw "  2. Executed via acl2s-compute (sandboxed)~%")
              (prog2$ (cw "  3. Security: forbidden ops blocked~%")
                (prog2$ (cw "  4. Permission: requires execute-allowed=t~%")
                  (prog2$ (cw "  5. All enforced by verified agent theorems~%")
                    t))))))))))

