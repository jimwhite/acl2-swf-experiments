; Test the LLM client
; Run with: cert.pl test-llm
; 
; Make sure LM Studio is running on http://host.docker.internal:1234
(in-package "ACL2")

;; Load the LLM client
(include-book "llm-client" 
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json) (:llm-client)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test 1: List available models (OpenAI compat - IDs only)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (mv-let (err models state)
   (llm-list-models state)
   (declare (ignorable state))
   (prog2$ 
    (if err
        (cw "~%LIST MODELS ERROR: ~x0~%" err)
      (cw "~%AVAILABLE MODEL IDs (OpenAI compat):~%~x0~%" models))
    (mv nil '(value-triple :list-ok) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test 2: List models with full info (LM Studio v0 API)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable state))
   (prog2$ 
    (if err
        (cw "~%FULL MODEL INFO ERROR: ~x0~%" err)
      (progn$
       (cw "~%FULL MODEL INFO (LM Studio v0 API):~%")
       (cw "  Total models: ~x0~%" (len models))
       (cw "  Loaded completions: ~x0~%" 
           (len (filter-loaded-completions-models models)))))
    (mv nil '(value-triple :full-ok) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test 3: Select best model with preferences
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Preferences in order - first match wins
(defconst *model-prefs* '("qwen" "nemotron" "llama"))

(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable state))
   (prog2$ 
    (if err
        (cw "~%SELECT MODEL ERROR: ~x0~%" err)
      (let ((selected (select-completions-model models *model-prefs*)))
        (if selected
            (cw "~%SELECTED MODEL: ~s0 (loaded ctx: ~x1)~%" 
                (model-info->id selected)
                (model-info->loaded-context-length selected))
          (cw "~%NO SUITABLE MODEL FOUND~%"))))
    (mv nil '(value-triple :select-ok) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test 4: Chat completion with selected model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *test-messages*
  (list (make-chat-message :role (chat-role-user)
                           :content "What is 2+2? Answer in one word.")))

(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable err))
   (let ((selected (select-completions-model models *model-prefs*)))
     (if (not selected)
         (prog2$ (cw "~%NO MODEL TO TEST~%")
                 (mv nil '(value-triple :no-model) state))
       (mv-let (err2 response state)
         (llm-chat-completion (model-info->id selected) *test-messages* state)
         (declare (ignorable state))
         (prog2$ 
          (if err2
              (cw "~%CHAT ERROR: ~x0~%" err2)
            (cw "~%CHAT RESPONSE: ~s0~%" response))
          (mv nil '(value-triple :chat-ok) state)))))))

(value-triple :test-complete)

