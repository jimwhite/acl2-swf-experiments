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
  "You are a helpful AI assistant with access to ACL2 code execution tools.

AVAILABLE TOOLS:
1. acl2-evaluate: Evaluate ACL2 expressions (e.g., (+ 1 2 3), (car '(a b c)))
2. acl2-admit: Test if a function definition is valid (e.g., (defun foo (x) (+ x 1)))
3. acl2-prove: Attempt to prove a theorem (e.g., (defthm my-thm (equal (+ a b) (+ b a))))

TOOL CALL FORMAT:
When you want to use a tool, respond with EXACTLY this format on its own line:
TOOL_CALL: tool-name | code-to-execute

Examples:
TOOL_CALL: acl2-evaluate | (+ 1 2 3)
TOOL_CALL: acl2-admit | (defun double (x) (* 2 x))
TOOL_CALL: acl2-prove | (defthm plus-comm (equal (+ a b) (+ b a)))

After seeing tool results, you can make more tool calls or provide a final answer.
When you have enough information, respond normally without TOOL_CALL.

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

;; Parse a tool call from LLM output
;; Returns (mv found? tool-name code) where found? indicates if TOOL_CALL was found
(defun parse-tool-call (response)
  (declare (xargs :mode :program))
  (let* ((prefix "TOOL_CALL:")
         (pos (search prefix response)))
    (if (not pos)
        (mv nil nil nil)
      ;; Found TOOL_CALL: - extract the rest of that line
      (let* ((start (+ pos (length prefix)))
             (rest (subseq response start (length response)))
             ;; Find end of line
             (newline-pos (search (coerce '(#\Newline) 'string) rest))
             (line (if newline-pos
                       (subseq rest 0 newline-pos)
                     rest))
             ;; Parse "tool-name | code"
             (pipe-pos (search "|" line)))
        (if (not pipe-pos)
            (mv nil nil nil)
          (let* ((tool-str (my-string-trim (subseq line 0 pipe-pos)))
                 (code-str (my-string-trim (subseq line (1+ pipe-pos) (length line)))))
            (mv t tool-str code-str)))))))

;;;============================================================================
;;; Execute Tool Call via MCP
;;;============================================================================

;; Execute a tool call using the MCP client
;; Returns (mv error-string result-string state)
(defun execute-tool-call (tool-name code mcp-conn state)
  (declare (xargs :mode :program :stobjs state))
  (if (not (mcp-connection-p mcp-conn))
      (mv "No MCP connection" "" state)
    (cond
      ((equal tool-name "acl2-evaluate")
       (mcp-acl2-evaluate mcp-conn code state))
      ((equal tool-name "acl2-admit")
       (mcp-acl2-admit mcp-conn code state))
      ((equal tool-name "acl2-prove")
       (mcp-acl2-prove mcp-conn code state))
      (t
       (mv (concatenate 'string "Unknown tool: " tool-name) "" state)))))

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
       
       ;; Parse for tool call
       ((mv found? tool-name code) (parse-tool-call response))
       
       ;; Add assistant message to conversation
       (agent-st (add-assistant-msg response agent-st)))
    
    (if (not found?)
        ;; No tool call - agent is done, return final response
        (mv nil nil (change-runtime-state rst :agent agent-st) state)
      ;; Execute tool call
      (b* ((- (cw "~%[Executing ~s0: ~s1]~%" tool-name code))
           ((mv tool-err result state)
            (execute-tool-call tool-name code mcp-conn state))
           
           (tool-result (if tool-err
                            (concatenate 'string "Error: " tool-err)
                          result))
           (- (cw "~%Tool result: ~s0~%" 
                  (if (> (length tool-result) 200)
                      (concatenate 'string (subseq tool-result 0 200) "...")
                    tool-result)))
           
           ;; Add tool result to conversation
           (agent-st (add-tool-result tool-result agent-st))
           
           ;; Increment step counter
           (agent-st (increment-step agent-st)))
        ;; Continue since we made a tool call
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
