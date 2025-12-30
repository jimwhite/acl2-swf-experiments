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
; and parsing functions used by the LLM client.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

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
;; JSON Parsing (Simple extraction for OpenAI response format)
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-json-string-value (json key)
  "Simple extraction of string value for KEY from JSON.
   Looks for \"key\":\"value\" or \"key\": \"value\" patterns.
   Returns the value string or NIL if not found."
  (let* ((key-pattern (format nil "\"~A\"" key))
         (key-pos (search key-pattern json)))
    (when key-pos
      (let* ((after-key (+ key-pos (length key-pattern)))
             ;; Skip whitespace and colon
             (colon-pos (position #\: json :start after-key)))
        (when colon-pos
          (let ((quote-start (position #\" json :start (1+ colon-pos))))
            (when quote-start
              (let ((value-start (1+ quote-start)))
                ;; Find closing quote (handling escapes)
                (let ((value-end nil)
                      (i value-start)
                      (len (length json)))
                  (loop while (and (< i len) (null value-end)) do
                    (let ((c (char json i)))
                      (cond
                        ((char= c #\\) (incf i 2))  ; skip escaped char
                        ((char= c #\") (setf value-end i))
                        (t (incf i)))))
                  (when value-end
                    ;; Unescape the value
                    (let ((raw (subseq json value-start value-end)))
                      ;; Simple unescaping
                      (with-output-to-string (out)
                        (let ((i 0) (len (length raw)))
                          (loop while (< i len) do
                            (let ((c (char raw i)))
                              (if (and (char= c #\\) (< (1+ i) len))
                                  (let ((next (char raw (1+ i))))
                                    (case next
                                      (#\" (write-char #\" out))
                                      (#\\ (write-char #\\ out))
                                      (#\n (write-char #\Newline out))
                                      (#\r (write-char #\Return out))
                                      (#\t (write-char #\Tab out))
                                      (otherwise 
                                       (write-char c out)
                                       (write-char next out)))
                                    (incf i 2))
                                  (progn
                                    (write-char c out)
                                    (incf i))))))))))))))))))

(defun parse-chat-response (json)
  "Parse OpenAI chat completion response, extract assistant content.
   Returns the content string, or empty string on parse failure."
  (or (find-json-string-value json "content")
      ""))

