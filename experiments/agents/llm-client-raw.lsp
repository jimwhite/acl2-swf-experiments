;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-

; LLM Client -- Raw Lisp Implementation for JSON serialization/parsing
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance
;
; This file provides raw Lisp implementations for JSON serialization
; and response parsing using Kestrel's json-parser library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note: The Kestrel JSON parser is loaded via include-book in llm-client.lisp
;; which makes parse-string-as-json available here.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON String Escaping
;;
;; Escape special characters in strings for JSON encoding.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun json-escape-string (s)
  "Escape special characters in string S for JSON encoding."
  (with-output-to-string (out)
    (loop for c across s do
      (case c
        (#\" (write-string "\\\"" out))
        (#\\ (write-string "\\\\" out))
        (#\Newline (write-string "\\n" out))
        (#\Return (write-string "\\r" out))
        (#\Tab (write-string "\\t" out))
        (otherwise 
         (if (< (char-code c) 32)
             ;; Control characters as \uXXXX
             (format out "\\u~4,'0X" (char-code c))
             (write-char c out)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON Serialization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun serialize-chat-message (msg)
  "Serialize a chat-message to JSON object string."
  ;; msg is (role . content) where role is FTY tagged sum
  ;; chat-message-p layout is :list, so msg = (role content)
  (let* ((role (car msg))
         (content (cadr msg))
         ;; Extract role string from FTY tagsum
         ;; chat-role is (:system), (:user), (:assistant), or (:tool)
         (role-str (case (car role)
                     (:system "system")
                     (:user "user")
                     (:assistant "assistant")
                     (:tool "tool")
                     (otherwise "user"))))
    (format nil "{\"role\":\"~A\",\"content\":\"~A\"}"
            role-str
            (json-escape-string (if (stringp content) content "")))))

(defun serialize-chat-messages (messages)
  "Serialize a list of chat-messages to JSON array string."
  (if (null messages)
      "[]"
      (format nil "[~{~A~^,~}]"
              (mapcar #'serialize-chat-message messages))))

(defun serialize-chat-request (model messages)
  "Serialize a chat completion request to JSON string."
  (format nil "{\"model\":\"~A\",\"messages\":~A}"
          (json-escape-string model)
          (serialize-chat-messages messages)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON Response Parsing (using Kestrel json-parser)
;;
;; OpenAI response format:
;; {
;;   "choices": [
;;     {
;;       "message": {
;;         "role": "assistant",
;;         "content": "response text here"
;;       }
;;     }
;;   ]
;; }
;;
;; Parsed structure from kestrel/json-parser:
;; (:OBJECT (("choices" :ARRAY ((:OBJECT (("message" :OBJECT (...))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-chat-content (parsed)
  "Extract assistant content from parsed OpenAI chat response structure."
  (and (consp parsed)
       (eq (car parsed) :object)
       (consp (cdr parsed))
       (let* ((pairs (cadr parsed))
              (choices-entry (assoc "choices" pairs :test #'equal)))
         (and choices-entry
              (consp (cdr choices-entry))
              (eq (cadr choices-entry) :array)
              (consp (cddr choices-entry))
              (consp (caddr choices-entry))
              (let ((first-choice (car (caddr choices-entry))))
                (and (consp first-choice)
                     (eq (car first-choice) :object)
                     (consp (cdr first-choice))
                     (let* ((choice-pairs (cadr first-choice))
                            (message-entry (assoc "message" choice-pairs :test #'equal)))
                       (and message-entry
                            (consp (cdr message-entry))
                            (eq (cadr message-entry) :object)
                            (consp (cddr message-entry))
                            (let* ((msg-pairs (caddr message-entry))
                                   (content-entry (assoc "content" msg-pairs :test #'equal)))
                              (and content-entry
                                   (stringp (cdr content-entry))
                                   (cdr content-entry)))))))))))

(defun parse-chat-response (json)
  "Parse OpenAI chat completion response, extract assistant content.
   Uses Kestrel json-parser for robust JSON handling.
   Returns the content string, or empty string on parse failure."
  (multiple-value-bind (err parsed)
      (parse-string-as-json json)
    (if err
        ""
        (or (extract-chat-content parsed) ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Models List Parsing
;;
;; GET /v1/models response format:
;; {
;;   "data": [
;;     {"id": "model-name-1", "object": "model", ...},
;;     {"id": "model-name-2", "object": "model", ...}
;;   ],
;;   "object": "list"
;; }
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-model-ids (parsed)
  "Extract model IDs from parsed /v1/models response.
   Returns a list of model ID strings."
  (and (consp parsed)
       (eq (car parsed) :object)
       (consp (cdr parsed))
       (let* ((pairs (cadr parsed))
              (data-entry (assoc "data" pairs :test #'equal)))
         (and data-entry
              (consp (cdr data-entry))
              (eq (cadr data-entry) :array)
              (consp (cddr data-entry))
              ;; Map over the array elements to extract "id" fields
              (loop for model-obj in (caddr data-entry)
                    when (and (consp model-obj)
                              (eq (car model-obj) :object)
                              (consp (cdr model-obj)))
                    collect (let* ((model-pairs (cadr model-obj))
                                   (id-entry (assoc "id" model-pairs :test #'equal)))
                              (if (and id-entry (stringp (cdr id-entry)))
                                  (cdr id-entry)
                                  "")))))))

(defun parse-models-response (json)
  "Parse /v1/models response, extract list of model IDs.
   Uses Kestrel json-parser for robust JSON handling.
   Returns list of model ID strings, or NIL on parse failure."
  (multiple-value-bind (err parsed)
      (parse-string-as-json json)
    (if err
        nil
        (or (extract-model-ids parsed) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LM Studio v0 API Models Parsing
;;
;; GET /api/v0/models response format:
;; {
;;   "data": [
;;     {
;;       "id": "model-name",
;;       "type": "llm",           ; or "vlm", "embeddings"
;;       "state": "loaded",       ; or "not-loaded"
;;       "publisher": "...",
;;       "arch": "...",
;;       "quantization": "...",
;;       "max_context_length": 131072,
;;       "loaded_context_length": 4096  ; only when loaded
;;     },
;;     ...
;;   ]
;; }
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-v0-model-info (model-obj)
  "Extract model-info from a single parsed model object.
   Returns a model-info-p structure."
  (if (and (consp model-obj)
           (eq (car model-obj) :object)
           (consp (cdr model-obj)))
      (let* ((pairs (cadr model-obj))
             (id (cdr (assoc "id" pairs :test #'equal)))
             (type-str (cdr (assoc "type" pairs :test #'equal)))
             (state-str (cdr (assoc "state" pairs :test #'equal)))
             (publisher (cdr (assoc "publisher" pairs :test #'equal)))
             (arch (cdr (assoc "arch" pairs :test #'equal)))
             (quant (cdr (assoc "quantization" pairs :test #'equal)))
             (max-ctx (cdr (assoc "max_context_length" pairs :test #'equal)))
             (loaded-ctx (cdr (assoc "loaded_context_length" pairs :test #'equal))))
        (make-model-info
         :id (if (stringp id) id "")
         :type (string-to-model-type (if (stringp type-str) type-str "llm"))
         :load-state (string-to-model-state (if (stringp state-str) state-str "not-loaded"))
         :publisher (if (stringp publisher) publisher "")
         :arch (if (stringp arch) arch "")
         :quantization (if (stringp quant) quant "")
         :max-context-length (if (integerp max-ctx) (max 0 max-ctx) 0)
         :loaded-context-length (if (integerp loaded-ctx) (max 0 loaded-ctx) 0)))
      ;; Return default empty model-info for malformed input
      (make-model-info :type (model-type-llm) :load-state (model-state-not-loaded))))

(defun extract-v0-models (parsed)
  "Extract list of model-info from parsed /api/v0/models response.
   Returns a model-info-list-p."
  (if (and (consp parsed)
           (eq (car parsed) :object)
           (consp (cdr parsed)))
      (let* ((pairs (cadr parsed))
             (data-entry (assoc "data" pairs :test #'equal)))
        (if (and data-entry
                 (consp (cdr data-entry))
                 (eq (cadr data-entry) :array)
                 (consp (cddr data-entry)))
            (loop for model-obj in (caddr data-entry)
                  collect (extract-v0-model-info model-obj))
            nil))
      nil))

(defun parse-v0-models-response (json)
  "Parse /api/v0/models response, extract full model info list.
   Uses Kestrel json-parser for robust JSON handling.
   Returns model-info-list-p, or NIL on parse failure."
  (multiple-value-bind (err parsed)
      (parse-string-as-json json)
    (if err
        nil
        (or (extract-v0-models parsed) nil))))

;; Re-export find-matching-model in raw Lisp since it uses LOOP
(defun find-matching-model (models prefs)
  "Find first model in MODELS whose ID contains any of PREFS as substring."
  (if (endp prefs)
      nil
    (let ((pref (car prefs)))
      (or (loop for m in models
                when (search pref (model-info->id m))
                return m)
          (find-matching-model models (cdr prefs))))))

(defun select-completions-model (models prefs)
  "Select best model for completions from MODELS based on PREFS.
   Returns first loaded completions model matching a pref, or first loaded
   completions model if no match."
  (let ((candidates (filter-loaded-completions-models models)))
    (or (and prefs (find-matching-model candidates prefs))
        (car candidates))))

