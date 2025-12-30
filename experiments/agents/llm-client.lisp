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
(include-book "http-json" 
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json)))
(include-book "std/strings/explode-nonnegative-integer" :dir :system)
(include-book "kestrel/json-parser/parse-json" :dir :system)
; (depends-on "llm-client-raw.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Configuration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *lm-studio-endpoint* 
  "http://host.docker.internal:1234/v1/chat/completions")

;; OpenAI-compatible models endpoint (basic info only)
(defconst *lm-studio-models-endpoint*
  "http://host.docker.internal:1234/v1/models")

;; LM Studio native API (full model info with type, state, context length)
(defconst *lm-studio-v0-models-endpoint*
  "http://host.docker.internal:1234/api/v0/models")

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

;; Parse models response JSON, extract list of model IDs
;; Input: json response string from /v1/models (OpenAI format)
;; Output: list of model ID strings (nil on parse failure)
;; Note: Implementation in llm-client-raw.lsp uses kestrel/json-parser
(defun parse-models-response (json)
  (declare (xargs :guard (stringp json))
           (ignore json))
  (prog2$ (er hard? 'parse-models-response "Raw Lisp definition not installed?")
          nil))

(defthm string-listp-of-parse-models-response
  (string-listp (parse-models-response json)))

;; Parse LM Studio v0 models response JSON, extract full model info
;; Input: json response string from /api/v0/models 
;; Output: list of model-info-p (nil on parse failure)
;; Note: Implementation in llm-client-raw.lsp uses kestrel/json-parser
(defun parse-v0-models-response (json)
  (declare (xargs :guard (stringp json))
           (ignore json))
  (prog2$ (er hard? 'parse-v0-models-response "Raw Lisp definition not installed?")
          nil))

(defthm model-info-list-p-of-parse-v0-models-response
  (model-info-list-p (parse-v0-models-response json)))

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

;; List available models from LLM server
;;
;; Parameters:
;;   state - ACL2 state
;;
;; Returns: (mv error models state)
;;   error  - NIL on success, error string on failure
;;   models - List of model ID strings (string-listp)
;;   state  - Updated state
(defun llm-list-models (state)
  (declare (xargs :stobjs state))
  (b* (;; HTTP headers for JSON API
       (headers '(("Accept" . "application/json")))
       
       ;; Make HTTP GET request
       ((mv err response-body status-raw state)
        (get-json *lm-studio-models-endpoint*
                  headers
                  *llm-connect-timeout*
                  *llm-read-timeout*
                  state))
       
       ;; Coerce status to natp
       (status (mbe :logic (nfix status-raw) :exec status-raw))
       
       ;; Check for network/connection errors
       ((when err)
        (mv err nil state))
       
       ;; Check for HTTP error status
       ((unless (http-success-p status))
        (mv (concatenate 'string "HTTP error: status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string))
            nil
            state))
       
       ;; Parse the response JSON to extract model list
       (models (parse-models-response response-body)))
    
    (mv nil models state)))

;; Return type theorems for llm-list-models
(defthm string-listp-of-llm-list-models-models
  (string-listp (mv-nth 1 (llm-list-models state))))

(defthm state-p1-of-llm-list-models
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (llm-list-models state)))))

;; List available models with full info from LM Studio v0 API
;;
;; Parameters:
;;   state - ACL2 state
;;
;; Returns: (mv error models state)
;;   error  - NIL on success, error string on failure
;;   models - List of model-info-p with full details
;;   state  - Updated state
(defun llm-list-models-full (state)
  (declare (xargs :stobjs state))
  (b* (;; HTTP headers for JSON API
       (headers '(("Accept" . "application/json")))
       
       ;; Make HTTP GET request to v0 API
       ((mv err response-body status-raw state)
        (get-json *lm-studio-v0-models-endpoint*
                  headers
                  *llm-connect-timeout*
                  *llm-read-timeout*
                  state))
       
       ;; Coerce status to natp
       (status (mbe :logic (nfix status-raw) :exec status-raw))
       
       ;; Check for network/connection errors
       ((when err)
        (mv err nil state))
       
       ;; Check for HTTP error status
       ((unless (http-success-p status))
        (mv (concatenate 'string "HTTP error: status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string))
            nil
            state))
       
       ;; Parse the response JSON to extract full model info
       (models (parse-v0-models-response response-body)))
    
    (mv nil models state)))

;; Return type theorems for llm-list-models-full
(defthm model-info-list-p-of-llm-list-models-full-models
  (model-info-list-p (mv-nth 1 (llm-list-models-full state))))

(defthm state-p1-of-llm-list-models-full
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (llm-list-models-full state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Model Selection
;;
;; Select the best model from available models based on preferences.
;; Default: first loaded completions model that matches any preference string.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check if model ID contains a preference substring (case-insensitive would be 
;; nice but we'll do exact substring for now)
(defun model-matches-pref-p (model-id pref)
  (declare (xargs :guard (and (stringp model-id) (stringp pref))))
  (search pref model-id))

;; Find first model matching any of the preferences
;; Implementation in raw Lisp uses LOOP for efficiency
(defun find-matching-model (models prefs)
  (declare (xargs :guard (and (model-info-list-p models)
                              (string-listp prefs)))
           (ignore models prefs))
  (prog2$ (er hard? 'find-matching-model "Raw Lisp definition not installed?")
          nil))

;; Select best model for completions
;;
;; Parameters:
;;   models - Full model info list from llm-list-models-full
;;   prefs  - List of preference strings to match (partial match on model ID)
;;
;; Returns: model-info-p or nil if no suitable model found
;;
;; Selection order:
;; 1. First loaded completions model matching a preference (in pref order)
;; 2. First loaded completions model (if no prefs or no match)
;; 3. NIL if no loaded completions models
(defun select-completions-model (models prefs)
  (declare (xargs :guard (and (model-info-list-p models)
                              (string-listp prefs)))
           (ignore models prefs))
  (prog2$ (er hard? 'select-completions-model "Raw Lisp definition not installed?")
          nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trust tag and raw Lisp inclusion for serialization functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :llm-client)
(include-raw "llm-client-raw.lsp"
             :host-readtable t)

