; LLM Client -- HTTP client for LLM API calls
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance
;
; This book provides a verified LLM client using properly-guarded HTTP JSON
; functions. All guards are maintained for formal verification.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "llm-types")
(include-book "http-json")
(include-book "std/strings/explode-nonnegative-integer" :dir :system)
(include-book "kestrel/json-parser/parse-json" :dir :system)
; (depends-on "llm-client-raw.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Configuration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *lm-studio-endpoint* 
  "http://host.docker.internal:1234/v1/chat/completions")

(defconst *llm-connect-timeout* 30)   ; seconds
(defconst *llm-read-timeout* 120)     ; seconds (higher for slow local models)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON Serialization Helpers
;;
;; Logical specifications - raw Lisp provides actual implementation.
;; These maintain proper guards (stringp returns).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize a single chat message to JSON object string
;; Input: chat-message-p
;; Output: stringp like {"role":"user","content":"hello"}
(defun serialize-chat-message (msg)
  (declare (xargs :guard (chat-message-p msg))
           (ignore msg))
  (prog2$ (er hard? 'serialize-chat-message "Raw Lisp definition not installed?")
          "{}"))

(defthm stringp-of-serialize-chat-message
  (stringp (serialize-chat-message msg)))

;; Serialize a list of chat messages to JSON array string
;; Input: chat-message-list-p
;; Output: stringp like [{"role":"user","content":"hello"}]
(defun serialize-chat-messages (messages)
  (declare (xargs :guard (chat-message-list-p messages))
           (ignore messages))
  (prog2$ (er hard? 'serialize-chat-messages "Raw Lisp definition not installed?")
          "[]"))

(defthm stringp-of-serialize-chat-messages
  (stringp (serialize-chat-messages messages)))

;; Serialize full chat completion request to JSON string
;; Input: model (stringp), messages (chat-message-list-p)
;; Output: stringp like {"model":"...","messages":[...]}
(defun serialize-chat-request (model messages)
  (declare (xargs :guard (and (stringp model) (chat-message-list-p messages)))
           (ignore model messages))
  (prog2$ (er hard? 'serialize-chat-request "Raw Lisp definition not installed?")
          "{}"))

(defthm stringp-of-serialize-chat-request
  (stringp (serialize-chat-request model messages)))

;; Parse chat completion response JSON, extract assistant message content
;; Input: json response string
;; Output: content string (empty on parse failure)
;; Note: Implementation in llm-client-raw.lsp uses kestrel/json-parser
(defun parse-chat-response (json)
  (declare (xargs :guard (stringp json))
           (ignore json))
  (prog2$ (er hard? 'parse-chat-response "Raw Lisp definition not installed?")
          ""))

(defthm stringp-of-parse-chat-response
  (stringp (parse-chat-response json)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper to check if HTTP status indicates success (2xx)
(defun http-success-p (status)
  (declare (xargs :guard (natp status)))
  (and (>= status 200)
       (< status 300)))

(defthm booleanp-of-http-success-p
  (booleanp (http-success-p status))
  :rule-classes :type-prescription)

;; Call LLM chat completion API
;;
;; Parameters:
;;   model    - Model identifier string (e.g., "local-model")
;;   messages - Conversation history as chat-message-list
;;   state    - ACL2 state
;;
;; Returns: (mv error response state)
;;   error    - NIL on success, error string on failure
;;   response - Assistant's response content (stringp, empty on error)
;;   state    - Updated state
(defun llm-chat-completion (model messages state)
  (declare (xargs :guard (and (stringp model)
                              (chat-message-list-p messages))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (disable post-json)))))
  (b* (;; Serialize the request to JSON
       (request-json (serialize-chat-request model messages))
       
       ;; HTTP headers for JSON API
       (headers '(("Content-Type" . "application/json")
                  ("Accept" . "application/json")))
       
       ;; Make HTTP POST request with proper guards
       ((mv err response-body status-raw state)
        (post-json *lm-studio-endpoint*
                   request-json
                   headers
                   *llm-connect-timeout*
                   *llm-read-timeout*
                   state))
       
       ;; Coerce status to natp (it is, via theorem, but help guard verification)
       (status (mbe :logic (nfix status-raw) :exec status-raw))
       
       ;; Check for network/connection errors
       ((when err)
        (mv err "" state))
       
       ;; Check for HTTP error status
       ((unless (http-success-p status))
        (mv (concatenate 'string "HTTP error: status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string))
            ""
            state))
       
       ;; Parse the response JSON to extract assistant content
       (content (parse-chat-response response-body)))
    
    (mv nil content state)))

;; Return type theorems for llm-chat-completion
(defthm stringp-of-llm-chat-completion-response
  (stringp (mv-nth 1 (llm-chat-completion model messages state))))

(defthm state-p1-of-llm-chat-completion
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (llm-chat-completion model messages state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trust tag and raw Lisp inclusion for serialization functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :llm-client)
(include-raw "llm-client-raw.lsp"
             :host-readtable t)

