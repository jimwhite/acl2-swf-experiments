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

