; Test the LLM client
; Run with: acl2 < test-llm.lisp
; Or interactively: (ld "test-llm.lisp")
;
; Make sure LM Studio is running on http://host.docker.internal:1234
(in-package "ACL2")

;; Load the LLM client
(include-book "llm-client")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test 1: List available models
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (mv-let (err models state)
   (llm-list-models state)
   (declare (ignorable state))
   (prog2$ 
    (if err
        (cw "~%LIST MODELS ERROR: ~x0~%" err)
      (cw "~%AVAILABLE MODELS:~%~x0~%" models))
    (mv nil '(value-triple :list-ok) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test 2: Chat completion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Model name - query available models with:
;;   curl http://host.docker.internal:1234/v1/models
(defconst *model* "nvidia/nemotron-3-nano")

;; Define test messages
(defconst *test-messages*
  (list (make-chat-message :role (chat-role-user)
                           :content "What is 2+2? Answer in one word.")))

;; Call the LLM and print results
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model* *test-messages* state)
   (declare (ignorable state))
   (prog2$ 
    (if err
        (cw "~%ERROR: ~x0~%" err)
      (cw "~%RESPONSE: ~s0~%" response))
    (mv nil '(value-triple :ok) state))))

(value-triple :test-complete)
