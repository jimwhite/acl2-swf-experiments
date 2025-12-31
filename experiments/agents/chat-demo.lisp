; Chat Demo - Interactive Verified Agent
; ======================================
; Load this file in ACL2, then execute each section in order.
; Each "cell" is marked with a comment header.
;
; Usage (interactive):
;   cd /workspaces/acl2-swf-experiments/experiments/agents
;   acl2
;   (ld "chat-demo.lisp")
;
; Usage (certification):
;   cert.pl chat-demo --acl2-cmd 'env SKIP_INTERACTIVE=1 acl2'
;   or just: cert.pl chat-demo  (uses cert_env below)
;
; The interactive parts (LLM calls, dynamic defconsts) are skipped
; during certification using #-skip-interactive reader conditionals.

; cert_param: (cert_env "SKIP_INTERACTIVE=1")

(in-package "ACL2")

;;;============================================================================
;;; Cell 1: Load the verified agent and LLM client
;;;============================================================================

;; Use full paths for ACL2-MCP compatibility
;; Trust tags needed for quicklisp/HTTP client
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/verified-agent")
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/llm-client"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) (:http-json) (:llm-client)))
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/mcp-client"
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json) (:mcp-client)))

;;;============================================================================
;;; Cell 2: Configuration - Auto-select best available model
;;;============================================================================

;; Model preferences in order - first match wins
(defconst *model-prefs* '("qwen" "nemotron" "llama" "gemma"))

;; Get full model info and select best loaded completions model
#-skip-interactive
(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (prog2$ 
    (if err
        (cw "~%Error getting models: ~s0~%" err)
      (progn$
       (cw "~%Available models: ~x0~%" (len models))
       (cw "Loaded completions models: ~x0~%" 
           (len (filter-loaded-completions-models models)))))
    (mv nil '(value-triple :models-listed) state))))

;; Select the best model based on preferences
#-skip-interactive
(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable err))
   (let ((selected (select-completions-model models *model-prefs*)))
     (prog2$
      (if selected
          (cw "~%Selected model: ~s0 (context: ~x1 tokens)~%"
              (model-info->id selected)
              (model-info->loaded-context-length selected))
        (cw "~%WARNING: No suitable model found! Make sure LM Studio is running.~%"))
      (mv nil 
          `(defconst *model-id* 
             ,(if selected (model-info->id selected) "no-model-found"))
          state)))))

;;;============================================================================
;;; Cell 3: Create initial agent state
;;;============================================================================

(defconst *initial-state*
  (make-agent-state 
    :max-steps 20              ; Allow up to 20 conversation turns
    :token-budget 50000        ; Token budget for tool calls
    :time-budget 3600          ; 1 hour time budget
    :file-access 1             ; Read access to files
    :execute-allowed t         ; Code execution enabled!
    :max-context-tokens 8000   ; Context window size
    :satisfaction 0))          ; Starting satisfaction

;;;============================================================================
;;; Cell 4: Initialize conversation with system prompt
;;;============================================================================

(defconst *system-prompt*
  "You are a helpful AI assistant running inside a formally verified ReAct agent framework built in ACL2.

You have access to ACL2 code execution. To run ACL2 code, put it in a fenced code block:

```acl2
(+ 1 2 3)
```

or:

```lisp
(defun factorial (n) (if (zp n) 1 (* n (factorial (1- n)))))
```

I will execute the code and show you the result. You can then continue reasoning or give a final answer.

Be concise. Show your reasoning.")

(defconst *agent-v1*
  (init-agent-conversation *system-prompt* *initial-state*))

;; Verify the conversation was initialized
#-skip-interactive
(defconst *check-init*
  (prog2$ (cw "Agent initialized. Messages: ~x0~%" 
              (len (get-messages *agent-v1*)))
          t))

;;;============================================================================
;;; Cell 5: Helper function to display conversation
;;;============================================================================

(defun show-messages (msgs)
  (declare (xargs :mode :program))
  (if (endp msgs)
      nil
    (let* ((msg (car msgs))
           (role (chat-message->role msg))
           (content (chat-message->content msg))
           (role-str (chat-role-case role
                       :system "SYSTEM"
                       :user "USER"
                       :assistant "ASSISTANT"
                       :tool "TOOL")))
      (prog2$ (cw "~%[~s0]~%~s1~%" role-str content)
              (show-messages (cdr msgs))))))

(defun show-conversation (st)
  (declare (xargs :mode :program))
  (prog2$ (cw "~%========== Conversation ==========")
          (prog2$ (show-messages (get-messages st))
                  (cw "~%===================================~%"))))

;;;============================================================================
;;; Interactive conversation demo (skipped during certification)
;;;============================================================================

;;;============================================================================
;;; Cell 6: User Turn 1 - Add a user message
;;;============================================================================

#-skip-interactive
(defconst *agent-v2*
  (add-user-msg "Hello! Can you explain what a formally verified agent is?" 
                *agent-v1*))

;; Show the conversation so far
#-skip-interactive
(defconst *show-v2*
  (show-conversation *agent-v2*))

;;;============================================================================
;;; Cell 7: Get LLM response for Turn 1 and add to conversation
;;;============================================================================

;; This calls the LLM and adds the response to conversation
;; Requires LM Studio running!
#-skip-interactive
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *agent-v2*) state)
   (if err
       (prog2$ (cw "~%LLM Error: ~s0~%" err)
               (mv nil `(defconst *agent-v3* *agent-v2*) state))
     (prog2$ (cw "~%Assistant: ~s0~%" response)
             (mv nil `(defconst *agent-v3* 
                        (add-assistant-msg ,response *agent-v2*)) 
                 state)))))

;; Show updated conversation
#-skip-interactive
(defconst *show-v3*
  (show-conversation *agent-v3*))

;;;============================================================================
;;; Cell 8: User Turn 2 - Follow-up question
;;;============================================================================

#-skip-interactive
(defconst *agent-v4*
  (add-user-msg "What properties have been proven about this agent?" 
                *agent-v3*))

#-skip-interactive
(defconst *show-v4*
  (show-conversation *agent-v4*))

;;;============================================================================
;;; Cell 9: Get LLM response for Turn 2
;;;============================================================================

;; Call LLM and add response to conversation
#-skip-interactive
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *agent-v4*) state)
   (if err
       (prog2$ (cw "~%LLM Error: ~s0~%" err)
               (mv nil `(defconst *agent-v5* *agent-v4*) state))
     (prog2$ (cw "~%Assistant: ~s0~%" response)
             (mv nil `(defconst *agent-v5* 
                        (add-assistant-msg ,response *agent-v4*)) 
                 state)))))

#-skip-interactive
(defconst *show-v5*
  (show-conversation *agent-v5*))

;;;============================================================================
;;; Cell 10: User Turn 3 - Get LLM response
;;;============================================================================

#-skip-interactive
(defconst *agent-v6*
  (add-user-msg "That's impressive! How does the context management work?" 
                *agent-v5*))

;; Call LLM for Turn 3
#-skip-interactive
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *agent-v6*) state)
   (if err
       (prog2$ (cw "~%LLM Error: ~s0~%" err)
               (mv nil `(defconst *agent-v7* *agent-v6*) state))
     (prog2$ (cw "~%Assistant: ~s0~%" response)
             (mv nil `(defconst *agent-v7* 
                        (add-assistant-msg ,response *agent-v6*)) 
                 state)))))

#-skip-interactive
(defconst *show-v7*
  (show-conversation *agent-v7*))

;;;============================================================================
;;; Cell 11: Check context token usage
;;;============================================================================

#-skip-interactive
(defconst *context-check*
  (let* ((msgs (get-messages *agent-v7*))
         (char-len (messages-char-length msgs))
         (token-est (messages-token-estimate msgs))
         (max-tokens (agent-state->max-context-tokens *agent-v7*)))
    (prog2$ (cw "~%Context Usage:~%")
      (prog2$ (cw "  Total characters: ~x0~%" char-len)
        (prog2$ (cw "  Estimated tokens: ~x0~%" token-est)
          (prog2$ (cw "  Max tokens: ~x0~%" max-tokens)
            (prog2$ (cw "  Safety margin: ~x0~%" *context-safety-margin*)
              (cw "  Fits in context: ~x0~%" 
                  (messages-fit-p msgs max-tokens)))))))))

;;;============================================================================
;;; Cell 12: Simulate a tool result (demonstrates add-tool-result)
;;;============================================================================

;; Simulate calling a file-read tool
#-skip-interactive
(defconst *agent-with-tool*
  (add-tool-result 
    "File contents of verified-agent.lisp (first 500 chars):
; Verified ReAct Agent - ACL2 Implementation
; This file implements a formally verified ReAct agent...
(in-package \"ACL2\")
(include-book \"std/util/define\" :dir :system)
..." 
    *agent-v7*))

#-skip-interactive
(defconst *show-tool*
  (show-conversation *agent-with-tool*))

;;;============================================================================
;;; Cell 13: Interactive function for live chat
;;;============================================================================

;;;============================================================================
;;; Code Execution Support
;;;============================================================================

;; Strip leading whitespace from character list
#-skip-interactive
(defun strip-leading-ws (lst)
  (declare (xargs :mode :program))
  (if (endp lst) nil
    (if (member (car lst) '(#\Space #\Tab #\Newline #\Return))
        (strip-leading-ws (cdr lst))
      lst)))

;; Trim whitespace from string
#-skip-interactive
(defun my-string-trim (str)
  (declare (xargs :mode :program))
  (let* ((chars (coerce str 'list))
         (trimmed (strip-leading-ws chars))
         (rev-trimmed (strip-leading-ws (reverse trimmed))))
    (coerce (reverse rev-trimmed) 'string)))

;; Extract first ```acl2 or ```lisp code block from text
#-skip-interactive
(defun extract-code-block (response)
  (declare (xargs :mode :program))
  (let* ((acl2-start (search "```acl2" response))
         (lisp-start (search "```lisp" response))
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
      (let* ((content-start (+ start-pos (length start-marker)))
             (newline-pos (search (coerce '(#\Newline) 'string)
                                  (subseq response content-start (length response))))
             (code-start (if newline-pos (+ content-start newline-pos 1) content-start))
             (rest (subseq response code-start (length response)))
             (end-pos (search "```" rest)))
        (if (not end-pos)
            (mv nil "")
          (mv t (my-string-trim (subseq rest 0 end-pos))))))))

;; Execute ACL2 code via MCP, auto-detecting form type
#-skip-interactive
(defun execute-acl2-code (code mcp-conn state)
  (declare (xargs :mode :program :stobjs state))
  (if (not (mcp-connection-p mcp-conn))
      (mv "No MCP connection" "" state)
    (let* ((trimmed (my-string-trim code))
           (is-defun (and (>= (length trimmed) 6)
                          (equal (subseq trimmed 0 6) "(defun")))
           (is-defthm (and (>= (length trimmed) 7)
                           (equal (subseq trimmed 0 7) "(defthm")))
           (is-thm (and (>= (length trimmed) 4)
                        (equal (subseq trimmed 0 4) "(thm"))))
      (cond (is-defun (mcp-acl2-admit mcp-conn code state))
            ((or is-defthm is-thm) (mcp-acl2-prove mcp-conn code state))
            (t (mcp-acl2-evaluate mcp-conn code state))))))

;;;============================================================================
;;; Cell 13: Interactive function for live chat
;;;============================================================================

;; Use this function for interactive chatting
;; Call: (chat-turn "your message" *agent* *model-id* state)
;; Returns: (mv new-agent state)

;; ReAct step: call LLM, check for code, execute if found, loop until done
#-skip-interactive
(defun react-loop (agent-st model-id mcp-conn max-steps state)
  "Execute ReAct loop: LLM -> extract code -> execute -> repeat until no code block"
  (declare (xargs :mode :program :stobjs state))
  (if (zp max-steps)
      (prog2$ (cw "~%[Max steps reached]~%")
              (mv agent-st state))
    (mv-let (err response state)
      (llm-chat-completion model-id (get-messages agent-st) state)
      (if err
          (prog2$ (cw "~%LLM Error: ~s0~%" err)
                  (mv agent-st state))
        (let ((agent-st (add-assistant-msg response agent-st)))
          (prog2$ (cw "~%Assistant: ~s0~%" response)
            (mv-let (found? code)
              (extract-code-block response)
              (if (not found?)
                  ;; No code block - done with this turn
                  (mv agent-st state)
                ;; Execute code and continue
                (prog2$ (cw "~%[Executing: ~s0]~%" code)
                  (mv-let (exec-err result state)
                    (execute-acl2-code code mcp-conn state)
                    (let* ((tool-result (if exec-err
                                            (concatenate 'string "Error: " exec-err)
                                          result))
                           ;; Truncate long results for display
                           (display-result (if (> (length tool-result) 300)
                                               (concatenate 'string 
                                                 (subseq tool-result 0 300) "...")
                                             tool-result))
                           (agent-st (add-tool-result tool-result agent-st)))
                      (prog2$ (cw "~%Result: ~s0~%" display-result)
                        ;; Continue ReAct loop
                        (react-loop agent-st model-id mcp-conn (1- max-steps) state)))))))))))))

#-skip-interactive
(defun chat-turn (user-msg agent-st model-id mcp-conn state)
  "Execute one chat turn with ReAct: add user message, run ReAct loop"
  (declare (xargs :mode :program :stobjs state))
  (let ((st-with-user (add-user-msg user-msg agent-st)))
    (react-loop st-with-user model-id mcp-conn 5 state)))

;;;============================================================================
;;; Cell 14: Full ReAct step demonstration
;;;============================================================================

;; Create a tool spec for demonstration
#-skip-interactive
(defconst *read-file-tool*
  (make-tool-spec
    :name 'read-file
    :required-access 1      ; Needs read access
    :requires-execute nil
    :token-cost 100
    :time-cost 5))

;; Check if we can invoke this tool
#-skip-interactive
(defconst *can-read-file*
  (prog2$ (cw "~%Can invoke read-file tool: ~x0~%" 
              (can-invoke-tool-p *read-file-tool* *agent-v7*))
          (can-invoke-tool-p *read-file-tool* *agent-v7*)))

;; Simulate a ReAct step with conversation
#-skip-interactive
(defconst *agent-after-react*
  (if (and (not (must-respond-p *agent-v7*))
           (can-invoke-tool-p *read-file-tool* *agent-v7*))
      (react-step-with-conversation
        (agent-action-tool-call 'read-file "verified-agent.lisp")
        *read-file-tool*
        "I'll read the verified-agent.lisp file to show you the implementation."
        "File read successfully. Contents: (in-package ACL2)..."
        *agent-v7*)
    *agent-v7*))

#-skip-interactive
(defconst *show-react*
  (prog2$ (cw "~%After ReAct step:~%")
    (prog2$ (cw "  Step counter: ~x0~%" 
                (agent-state->step-counter *agent-after-react*))
      (prog2$ (cw "  Token budget: ~x0~%" 
                  (agent-state->token-budget *agent-after-react*))
        (cw "  Message count: ~x0~%" 
            (len (get-messages *agent-after-react*)))))))

;;;============================================================================
;;; Summary
;;;============================================================================

#-skip-interactive
(defconst *demo-complete*
  (prog2$ (cw "~%~%========================================~%")
    (prog2$ (cw "Chat Demo Complete!~%")
      (prog2$ (cw "========================================~%")
        (prog2$ (cw "~%Key points demonstrated:~%")
          (prog2$ (cw "  1. Agent state initialization~%")
            (prog2$ (cw "  2. Conversation management (add-user-msg, add-assistant-msg)~%")
              (prog2$ (cw "  3. Context length tracking~%")
                (prog2$ (cw "  4. Tool result handling~%")
                  (prog2$ (cw "  5. ReAct step with conversation~%")
                    (prog2$ (cw "  6. State preservation verification~%")
                      (cw "~%For live LLM chat, ensure LM Studio is running at:~%  http://host.docker.internal:1234~%"))))))))))))

;;;============================================================================
;;; Cell 15: Interactive Chat Loop
;;;============================================================================

;; Read a line from standard input character by character
#-skip-interactive
(defun read-line-chars (acc state)
  "Accumulate characters until newline or EOF."
  (declare (xargs :mode :program :stobjs state))
  (mv-let (char state)
    (read-char$ *standard-ci* state)
    (cond ((null char)  ; EOF
           (mv (if (null acc) nil (coerce (reverse acc) 'string)) state))
          ((eql char #\Newline)
           (mv (coerce (reverse acc) 'string) state))
          (t (read-line-chars (cons char acc) state)))))

#-skip-interactive
(defun read-line-from-user (state)
  "Read a line from standard input, return (mv line state)."
  (declare (xargs :mode :program :stobjs state))
  (read-line-chars nil state))

;; Helper must be defined before main function
#-skip-interactive
(defun interactive-chat-loop-aux (agent-st model-id mcp-conn state)
  "Helper for interactive chat loop with code execution."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%You: ")  ; prompt
    (mv-let (input state)
      (read-line-from-user state)
      (if (or (null input)
              (equal input "/exit")
              (equal input "/quit"))
          (prog2$ (cw "~%Goodbye!~%")
                  (mv agent-st state))
        (mv-let (new-agent state)
          (chat-turn input agent-st model-id mcp-conn state)
          (interactive-chat-loop-aux new-agent model-id mcp-conn state))))))

;; Interactive chat loop - runs until user types /exit
#-skip-interactive
(defun interactive-chat-loop (agent-st model-id state)
  "Run an interactive ReAct chat loop with code execution. Type /exit to quit."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%========================================~%")
    (prog2$ (cw "Interactive ReAct Chat with Code Execution~%")
      (prog2$ (cw "(type /exit to quit)~%")
        (prog2$ (cw "========================================~%")
          (prog2$ (cw "~%Connecting to MCP server...~%")
            (mv-let (mcp-err mcp-conn state)
              (mcp-connect *mcp-default-endpoint* state)
              (if mcp-err
                  (prog2$ (cw "MCP connection failed: ~s0~%" mcp-err)
                    (prog2$ (cw "Code execution disabled.~%")
                      (interactive-chat-loop-aux agent-st model-id nil state)))
                (prog2$ (cw "MCP connected.~%")
                  (prog2$ (if (mcp-connection-has-acl2-session-p mcp-conn)
                              (cw "ACL2 session: ~s0~%" 
                                  (mcp-connection->acl2-session-id mcp-conn))
                            (cw "Warning: No persistent ACL2 session (slower mode).~%"))
                    (interactive-chat-loop-aux agent-st model-id mcp-conn state)))))))))))

;; To start interactive chat after loading, run:
;; (interactive-chat-loop *agent-v1* *model-id* state)