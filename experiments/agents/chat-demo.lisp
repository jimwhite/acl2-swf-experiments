; Chat Demo - Interactive Verified Agent
; ======================================
; Load this file in ACL2, then execute each section in order.
; Each "cell" is marked with a comment header.
;
; Usage:
;   cd /workspaces/acl2-swf-experiments/experiments/agents
;   acl2
;   (ld "chat-demo.lisp")
;
; Or run cells individually after loading books.

(in-package "ACL2")

;;;============================================================================
;;; Cell 1: Load the verified agent and LLM client
;;;============================================================================

;; Use full paths for ACL2-MCP compatibility
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/verified-agent")
(include-book "/workspaces/acl2-swf-experiments/experiments/agents/llm-client")

;;;============================================================================
;;; Cell 2: Configuration - Auto-select best available model
;;;============================================================================

;; Model preferences in order - first match wins
(defconst *model-prefs* '("qwen" "nemotron" "llama" "gemma"))

;; Get full model info and select best loaded completions model
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
    :execute-allowed nil       ; No code execution
    :max-context-tokens 8000   ; Context window size
    :satisfaction 0))          ; Starting satisfaction

;;;============================================================================
;;; Cell 4: Initialize conversation with system prompt
;;;============================================================================

(defconst *system-prompt*
  "You are a helpful AI assistant running inside a formally verified agent framework built in ACL2. 
You can engage in conversation and help with questions.
Be concise but helpful in your responses.")

(defconst *agent-v1*
  (init-agent-conversation *system-prompt* *initial-state*))

;; Verify the conversation was initialized
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
;;; Cell 6: User Turn 1 - Add a user message
;;;============================================================================

(defconst *agent-v2*
  (add-user-msg "Hello! Can you explain what a formally verified agent is?" 
                *agent-v1*))

;; Show the conversation so far
(defconst *show-v2*
  (show-conversation *agent-v2*))

;;;============================================================================
;;; Cell 7: Get LLM response for Turn 1
;;;============================================================================

;; This actually calls the LLM - requires LM Studio running!
;; Call LLM and print the response
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *agent-v2*) state)
   (prog2$ 
    (if err
        (cw "~%LLM Error: ~s0~%" err)
      (cw "~%LLM Response:~%~s0~%" response))
    (mv nil '(value-triple :llm-called) state))))

;;;============================================================================
;;; Cell 8: Add assistant response to conversation
;;;============================================================================

;; NOTE: After running Cell 7, manually copy the response text here
;; Or use the response from the mv if you're running interactively

(defconst *assistant-response-1*
  "A formally verified agent is an AI system whose decision-making logic has been mathematically proven correct using a theorem prover like ACL2. This means properties like 'the agent will always respect permission boundaries' or 'the agent will eventually terminate' are guaranteed by proof, not just testing. The agent you're talking to right now has verified properties for permission safety, budget bounds, and termination!")

(defconst *agent-v3*
  (add-assistant-msg *assistant-response-1* *agent-v2*))

;; Show updated conversation
(defconst *show-v3*
  (show-conversation *agent-v3*))

;;;============================================================================
;;; Cell 9: Verify agent state is still valid
;;;============================================================================

(defconst *state-check-1*
  (prog2$ (cw "~%Agent State Check:~%")
    (prog2$ (cw "  agent-state-p: ~x0~%" (agent-state-p *agent-v3*))
      (prog2$ (cw "  must-respond-p: ~x0~%" (must-respond-p *agent-v3*))
        (prog2$ (cw "  should-continue-p: ~x0~%" (should-continue-p *agent-v3*))
          (prog2$ (cw "  step-counter: ~x0~%" (agent-state->step-counter *agent-v3*))
            (prog2$ (cw "  messages count: ~x0~%" (len (get-messages *agent-v3*)))
              (cw "  conversation-has-room-p: ~x0~%" 
                  (conversation-has-room-p *agent-v3*)))))))))

;;;============================================================================
;;; Cell 10: User Turn 2 - Follow-up question
;;;============================================================================

(defconst *agent-v4*
  (add-user-msg "What properties have been proven about this agent?" 
                *agent-v3*))

(defconst *show-v4*
  (show-conversation *agent-v4*))

;;;============================================================================
;;; Cell 11: Get LLM response for Turn 2
;;;============================================================================

;; Uncomment to call LLM:
;; (mv-let (err response state)
;;   (llm-chat-completion *model-id* (get-messages *agent-v4*) state)
;;   (if err
;;       (prog2$ (cw "~%LLM Error: ~s0~%" err)
;;               (mv "Error" state))
;;     (prog2$ (cw "~%LLM Response:~%~s0~%" response)
;;             (mv response state))))

(defconst *assistant-response-2*
  "Several key properties have been formally proven:

1. **Permission Safety** - The agent can only invoke tools it has permission for
2. **Budget Bounds** - Token and time budgets never go negative after deductions
3. **Termination** - The agent is guaranteed to stop (max steps, budget exhaustion, or completion)
4. **State Preservation** - All state transitions preserve the validity of agent state
5. **Conversation Preservation** - Adding messages doesn't affect control flow decisions

These aren't just tested - they're mathematically proven to hold for ALL possible inputs!")

(defconst *agent-v5*
  (add-assistant-msg *assistant-response-2* *agent-v4*))

(defconst *show-v5*
  (show-conversation *agent-v5*))

;;;============================================================================
;;; Cell 12: User Turn 3 - Test context management
;;;============================================================================

(defconst *agent-v6*
  (add-user-msg "That's impressive! How does the context management work?" 
                *agent-v5*))

(defconst *show-v6*
  (show-conversation *agent-v6*))

;;;============================================================================
;;; Cell 13: Check context token usage
;;;============================================================================

(defconst *context-check*
  (let* ((msgs (get-messages *agent-v6*))
         (char-len (messages-char-length msgs))
         (token-est (messages-token-estimate msgs))
         (max-tokens (agent-state->max-context-tokens *agent-v6*)))
    (prog2$ (cw "~%Context Usage:~%")
      (prog2$ (cw "  Total characters: ~x0~%" char-len)
        (prog2$ (cw "  Estimated tokens: ~x0~%" token-est)
          (prog2$ (cw "  Max tokens: ~x0~%" max-tokens)
            (prog2$ (cw "  Safety margin: ~x0~%" *context-safety-margin*)
              (cw "  Fits in context: ~x0~%" 
                  (messages-fit-p msgs max-tokens)))))))))

;;;============================================================================
;;; Cell 14: Simulate a tool result (demonstrates add-tool-result)
;;;============================================================================

;; Simulate calling a file-read tool
(defconst *agent-with-tool*
  (add-tool-result 
    "File contents of verified-agent.lisp (first 500 chars):
; Verified ReAct Agent - ACL2 Implementation
; This file implements a formally verified ReAct agent...
(in-package \"ACL2\")
(include-book \"std/util/define\" :dir :system)
..." 
    *agent-v6*))

(defconst *show-tool*
  (show-conversation *agent-with-tool*))

;;;============================================================================
;;; Cell 15: Interactive function for live chat
;;;============================================================================

;; Use this function for interactive chatting
;; Call: (chat "your message here" *current-agent-state*)
;; Returns: new agent state (bind to new constant)

(defun chat-turn (user-msg agent-st model-id state)
  "Execute one chat turn: add user message, call LLM, add response"
  (declare (xargs :mode :program :stobjs state))
  (let ((st-with-user (add-user-msg user-msg agent-st)))
    (mv-let (err response state)
      (llm-chat-completion model-id (get-messages st-with-user) state)
      (if err
          (prog2$ (cw "~%Error: ~s0~%" err)
                  (mv st-with-user state))
        (let ((st-with-response (add-assistant-msg response st-with-user)))
          (prog2$ (cw "~%Assistant: ~s0~%" response)
                  (mv st-with-response state)))))))

;; Example usage (uncomment to run):
;; (mv-let (new-agent state)
;;   (chat-turn "What is 2+2?" *agent-v1* *model-id* state)
;;   (mv (show-conversation new-agent) new-agent state))

;;;============================================================================
;;; Cell 16: Full ReAct step demonstration
;;;============================================================================

;; Create a tool spec for demonstration
(defconst *read-file-tool*
  (make-tool-spec
    :name 'read-file
    :required-access 1      ; Needs read access
    :requires-execute nil
    :token-cost 100
    :time-cost 5))

;; Check if we can invoke this tool
(defconst *can-read-file*
  (prog2$ (cw "~%Can invoke read-file tool: ~x0~%" 
              (can-invoke-tool-p *read-file-tool* *agent-v6*))
          (can-invoke-tool-p *read-file-tool* *agent-v6*)))

;; Simulate a ReAct step with conversation
(defconst *agent-after-react*
  (if (and (not (must-respond-p *agent-v6*))
           (can-invoke-tool-p *read-file-tool* *agent-v6*))
      (react-step-with-conversation
        (agent-action-tool-call 'read-file "verified-agent.lisp")
        *read-file-tool*
        "I'll read the verified-agent.lisp file to show you the implementation."
        "File read successfully. Contents: (in-package ACL2)..."
        *agent-v6*)
    *agent-v6*))

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
