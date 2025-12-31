; agent-runner.lisp - Runtime driver for verified agent with MCP code execution
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; This book provides the runtime integration between:
; - verified-agent.lisp (decision logic, state management)
; - llm-client.lisp (LLM chat completions)
; - mcp-client.lisp (code execution via acl2-mcp)
;
; The verified agent decides what to do; this runner executes it.

(in-package "ACL2")

;;;============================================================================
;;; Imports
;;;============================================================================

(include-book "verified-agent")
(include-book "llm-client"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client)))
(include-book "mcp-client"
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json) (:mcp-client)))

;;;============================================================================
;;; Tool Specifications for Code Execution
;;;============================================================================

;; ACL2 evaluate tool - runs arbitrary ACL2 expressions
(defconst *tool-acl2-evaluate*
  (make-tool-spec
    :name 'acl2-evaluate
    :required-access 0           ; No file access needed
    :requires-execute t          ; Requires execute permission
    :token-cost 100              ; Estimated tokens for result
    :time-cost 5))               ; Estimated seconds

;; ACL2 admit tool - test function definitions
(defconst *tool-acl2-admit*
  (make-tool-spec
    :name 'acl2-admit
    :required-access 0
    :requires-execute t
    :token-cost 200
    :time-cost 10))

;; ACL2 prove tool - attempt theorem proofs
(defconst *tool-acl2-prove*
  (make-tool-spec
    :name 'acl2-prove
    :required-access 0
    :requires-execute t
    :token-cost 500
    :time-cost 30))

;;;============================================================================
;;; System Prompt for Code Execution Agent
;;;============================================================================

(defconst *code-agent-system-prompt*
  "You are a helpful AI assistant with access to ACL2 code execution.

You can execute ACL2 code by putting it in a fenced code block with language 'acl2' or 'lisp'.

EXAMPLES:

To evaluate an expression:
```acl2
(+ 1 2 3)
```

To define and test a function:
```acl2
(defun factorial (n)
  (if (zp n) 1 (* n (factorial (1- n)))))
```

To prove a theorem:
```lisp
(defthm plus-comm
  (equal (+ a b) (+ b a)))
```

I will execute each code block and show you the result. You can then:
- Write more code blocks to continue exploring
- Give a final answer when you have enough information

Be concise. Show your reasoning.")

;;;============================================================================
;;; Runtime State - Holds MCP connection alongside agent state
;;;============================================================================

;; Runtime state bundles agent state with MCP connection
;; We use a simple product for now
(fty::defprod runtime-state
  ((agent agent-state-p)
   (mcp-conn t)           ; nil or mcp-connection-p (use t for flexibility)
   (model-id stringp :default ""))
  :layout :list)

;;;============================================================================
;;; Tool Call Parsing
;;;============================================================================

;; Helper: strip leading whitespace characters from list
(defun strip-leading-ws (lst)
  (declare (xargs :mode :program))
  (if (endp lst)
      nil
    (if (member (car lst) '(#\Space #\Tab #\Newline #\Return))
        (strip-leading-ws (cdr lst))
      lst)))

;; Strip leading/trailing whitespace from a string
(defun my-string-trim (str)
  (declare (xargs :mode :program))
  (let* ((chars (coerce str 'list))
         (trimmed (strip-leading-ws chars))
         (rev-trimmed (strip-leading-ws (reverse trimmed))))
    (coerce (reverse rev-trimmed) 'string)))

;; Extract first code block from LLM response
;; Looks for ```acl2 or ```lisp fenced blocks
;; Returns (mv found? code) where found? indicates if a code block was found
(defun extract-code-block (response)
  (declare (xargs :mode :program))
  (let* (;; Try ```acl2 first
         (acl2-start (search "```acl2" response))
         (lisp-start (search "```lisp" response))
         ;; Use whichever comes first (or exists)
         (start-marker (cond ((and acl2-start lisp-start)
                              (if (< acl2-start lisp-start) "```acl2" "```lisp"))
                             (acl2-start "```acl2")
                             (lisp-start "```lisp")
                             (t nil)))
         (start-pos (cond ((and acl2-start lisp-start)
                           (min acl2-start lisp-start))
                          (acl2-start acl2-start)
                          (lisp-start lisp-start)
                          (t nil))))
    (if (not start-pos)
        (mv nil "")
      ;; Found a code block start - find the content
      (let* ((content-start (+ start-pos (length start-marker)))
             ;; Skip to newline after ```acl2 or ```lisp
             (newline-pos (search (coerce '(#\Newline) 'string) 
                                  (subseq response content-start (length response))))
             (code-start (if newline-pos 
                             (+ content-start newline-pos 1)
                           content-start))
             ;; Find closing ```
             (rest (subseq response code-start (length response)))
             (end-pos (search "```" rest)))
        (if (not end-pos)
            (mv nil "")  ; No closing fence
          (mv t (my-string-trim (subseq rest 0 end-pos))))))))

;;;============================================================================
;;; Execute Code via MCP
;;;============================================================================

;; Determine what kind of ACL2 form this is and execute appropriately
;; Returns (mv error-string result-string state)
(defun execute-acl2-code (code mcp-conn state)
  (declare (xargs :mode :program :stobjs state))
  (if (not (mcp-connection-p mcp-conn))
      (mv "No MCP connection" "" state)
    ;; Detect form type from code
    (let* ((trimmed (my-string-trim code))
           (is-defun (and (>= (length trimmed) 6)
                          (equal (subseq trimmed 0 6) "(defun")))
           (is-defthm (and (>= (length trimmed) 7)
                           (equal (subseq trimmed 0 7) "(defthm")))
           (is-thm (and (>= (length trimmed) 4)
                        (equal (subseq trimmed 0 4) "(thm"))))
      (cond
        ;; Use admit for defun (test without saving)
        (is-defun
         (mcp-acl2-admit mcp-conn code state))
        ;; Use prove for defthm/thm
        ((or is-defthm is-thm)
         (mcp-acl2-prove mcp-conn code state))
        ;; Default: evaluate expression
        (t
         (mcp-acl2-evaluate mcp-conn code state))))))

;;;============================================================================
;;; Single Agent Step
;;;============================================================================

;; Execute one step of the agent loop:
;; 1. Call LLM with current conversation
;; 2. Parse response for tool call
;; 3. If tool call, execute and add result to conversation
;; 4. Update agent state
;; Returns (mv continue? error runtime-state acl2-state)
;; continue? is T if agent made a tool call, NIL if agent gave final answer
(defun agent-step (rst state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((agent-st (runtime-state->agent rst))
       (mcp-conn (runtime-state->mcp-conn rst))
       (model-id (runtime-state->model-id rst))
       
       ;; Check if agent should continue
       ((when (must-respond-p agent-st))
        (mv nil nil rst state))
       
       ;; Get LLM response
       ((mv llm-err response state)
        (llm-chat-completion model-id (get-messages agent-st) state))
       
       ((when llm-err)
        (mv nil llm-err rst state))
       
       (- (cw "~%Assistant: ~s0~%" response))
       
       ;; Extract code block from response
       ((mv found? code) (extract-code-block response))
       
       ;; Add assistant message to conversation
       (agent-st (add-assistant-msg response agent-st)))
    
    (if (not found?)
        ;; No code block - agent is done, return final response
        (mv nil nil (change-runtime-state rst :agent agent-st) state)
      ;; Execute the code
      (b* ((- (cw "~%[Executing ACL2 code:]~%~s0~%" code))
           ((mv tool-err result state)
            (execute-acl2-code code mcp-conn state))
           
           (tool-result (if tool-err
                            (concatenate 'string "Error: " tool-err)
                          result))
           (- (cw "~%Result: ~s0~%" 
                  (if (> (length tool-result) 200)
                      (concatenate 'string (subseq tool-result 0 200) "...")
                    tool-result)))
           
           ;; Add tool result to conversation
           (agent-st (add-tool-result tool-result agent-st))
           
           ;; Increment step counter
           (agent-st (increment-step agent-st)))
        ;; Continue since we executed code
        (mv t nil (change-runtime-state rst :agent agent-st) state)))))

;;;============================================================================
;;; Agent Loop
;;;============================================================================

;; Run agent loop until done or max steps
;; Returns (mv error runtime-state acl2-state)
(defun agent-loop (rst max-iterations state)
  (declare (xargs :mode :program :stobjs state))
  (if (zp max-iterations)
      (mv "Max iterations reached" rst state)
    (b* ((agent-st (runtime-state->agent rst))
         ((when (must-respond-p agent-st))
          (mv nil rst state))
         ;; agent-step returns (mv continue? err rst state)
         ((mv continue? err rst state) (agent-step rst state))
         ((when err)
          (mv err rst state))
         ;; If agent didn't make a tool call, it's done
         ((unless continue?)
          (mv nil rst state)))
      (agent-loop rst (1- max-iterations) state))))

;;;============================================================================
;;; Main Entry Point
;;;============================================================================

;; Initialize and run the code execution agent
;; Returns (mv error final-runtime-state acl2-state)
(defun run-code-agent (user-query model-id state)
  (declare (xargs :mode :program :stobjs state))
  (b* (;; Connect to MCP server
       (- (cw "~%Connecting to MCP server...~%"))
       ((mv mcp-err mcp-conn state)
        (mcp-connect *mcp-default-endpoint* state))
       
       ((when mcp-err)
        (prog2$ (cw "~%MCP connection failed: ~s0~%" mcp-err)
                (mv mcp-err nil state)))
       
       (- (cw "MCP connected: ~x0~%" mcp-conn))
       
       ;; Create initial agent state with code execution enabled
       (agent-st (make-agent-state
                   :max-steps 20
                   :token-budget 50000
                   :time-budget 3600
                   :file-access 0
                   :execute-allowed t    ; Enable code execution!
                   :max-context-tokens 8000
                   :satisfaction 0))
       
       ;; Initialize conversation
       (agent-st (init-agent-conversation *code-agent-system-prompt* agent-st))
       
       ;; Add user query
       (agent-st (add-user-msg user-query agent-st))
       
       ;; Create runtime state
       (rst (make-runtime-state
              :agent agent-st
              :mcp-conn mcp-conn
              :model-id model-id))
       
       (- (cw "~%Starting agent loop...~%"))
       (- (cw "~%User: ~s0~%" user-query))
       
       ;; Run the agent loop
       ((mv err rst state) (agent-loop rst 10 state)))
    
    (prog2$ (if err
                (cw "~%Agent finished with error: ~s0~%" err)
              (cw "~%Agent completed successfully.~%"))
            (mv err rst state))))

;;;============================================================================
;;; Quick Test Macro
;;;============================================================================

;; Usage: (test-code-agent "What is (+ 1 2 3)?" "your-model-id")
(defmacro test-code-agent (query model-id)
  `(make-event
    (mv-let (err rst state)
      (run-code-agent ,query ,model-id state)
      (declare (ignore err rst))
      (mv nil '(value-triple :agent-done) state))))
