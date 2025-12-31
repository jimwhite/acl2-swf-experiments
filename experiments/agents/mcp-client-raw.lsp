;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-

; MCP Client -- Raw Lisp Implementation
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance
;
; This file provides the raw Lisp implementation for MCP JSON-RPC serialization
; and response parsing. Uses cl-json for JSON handling.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON escaping helper
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-escape-json-string (s)
  "Escape a string for safe inclusion in JSON."
  (if (not (stringp s))
      ""
    (with-output-to-string (out)
      (loop for char across s do
            (case char
              (#\" (write-string "\\\"" out))
              (#\\ (write-string "\\\\" out))
              (#\Newline (write-string "\\n" out))
              (#\Return (write-string "\\r" out))
              (#\Tab (write-string "\\t" out))
              (otherwise 
               (if (< (char-code char) 32)
                   (format out "\\u~4,'0x" (char-code char))
                 (write-char char out))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; serialize-mcp-tool-call implementation
;;
;; Build JSON-RPC 2.0 request for MCP tools/call method
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun serialize-mcp-tool-call (tool-name args-json request-id)
  "Serialize MCP tool call to JSON-RPC 2.0 format."
  (if (not (and (stringp tool-name) (stringp args-json) (natp request-id)))
      "{}"
    ;; Build JSON-RPC request manually to avoid dependency on cl-json for encoding
    ;; Format: {"jsonrpc":"2.0","method":"tools/call","params":{"name":"...","arguments":{...}},"id":N}
    (format nil "{\"jsonrpc\":\"2.0\",\"method\":\"tools/call\",\"params\":{\"name\":\"~a\",\"arguments\":~a},\"id\":~d}"
            (mcp-escape-json-string tool-name)
            args-json  ; Already JSON object string
            request-id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; serialize-mcp-initialize implementation
;;
;; Build JSON-RPC 2.0 request for MCP initialize method
;; This is the first call to establish an MCP transport session
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun serialize-mcp-initialize (request-id)
  "Serialize MCP initialize request to JSON-RPC 2.0 format."
  (if (not (natp request-id))
      "{}"
    ;; Format: {"jsonrpc":"2.0","method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"acl2-mcp-client","version":"1.0"}},"id":N}
    (format nil "{\"jsonrpc\":\"2.0\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2024-11-05\",\"capabilities\":{},\"clientInfo\":{\"name\":\"acl2-mcp-client\",\"version\":\"1.0\"}},\"id\":~d}"
            request-id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; parse-mcp-session-id implementation
;;
;; Extract Mcp-Session-Id from response headers alist
;; Headers come in as ((key . value) ...) with lowercase keys
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun parse-mcp-session-id (headers-alist)
  "Extract mcp-session-id from response headers alist.
   Returns session-id string or nil if not found."
  (if (not (listp headers-alist))
      nil
    (let ((entry (assoc "mcp-session-id" headers-alist :test #'equal)))
      (if (and entry (stringp (cdr entry)))
          (cdr entry)
        nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; serialize-string-args implementation
;;
;; Build JSON object from alist of string pairs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun serialize-string-args (pairs)
  "Serialize alist of (string . string) pairs to JSON object."
  (if (not (listp pairs))
      "{}"
    (with-output-to-string (out)
      (write-char #\{ out)
      (loop for (pair . rest) on pairs
            for key = (if (consp pair) (car pair) "")
            for val = (if (consp pair) (cdr pair) "")
            do (progn
                 (write-char #\" out)
                 (write-string (if (stringp key) (mcp-escape-json-string key) "") out)
                 (write-string "\":\"" out)
                 (write-string (if (stringp val) (mcp-escape-json-string val) "") out)
                 (write-char #\" out)
                 (when rest (write-char #\, out))))
      (write-char #\} out))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; parse-mcp-response implementation  
;;
;; Parse JSON-RPC 2.0 response and extract result or error
;; Uses kestrel/json-parser (parse-string-as-json) which is loaded via http-json
;;
;; Kestrel JSON parser output format:
;; (:OBJECT (("key" . value) ...))  for objects
;; (:ARRAY (item1 item2 ...))       for arrays
;; Strings are plain strings, numbers are numbers, etc.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-json-get-object-pairs (parsed)
  "Get the alist of pairs from a parsed JSON object (:OBJECT pairs)."
  (if (and (consp parsed)
           (eq (car parsed) :object)
           (consp (cdr parsed)))
      (cadr parsed)
    nil))

(defun mcp-json-lookup (key pairs)
  "Look up a key in JSON object pairs alist."
  (if (not (and (stringp key) (listp pairs)))
      nil
    (let ((entry (assoc key pairs :test #'equal)))
      (if entry (cdr entry) nil))))

(defun mcp-extract-text-content (content-parsed)
  "Extract text from MCP content array.
   Input: (:ARRAY (item1 item2 ...)) where each item is (:OBJECT ((type . text) (text . content)))
   Output: concatenated text string"
  (if (not (and (consp content-parsed)
                (eq (car content-parsed) :array)
                (consp (cdr content-parsed))))
      ""
    (let ((items (cadr content-parsed)))
      (with-output-to-string (out)
        (loop for item in items
              for pairs = (mcp-json-get-object-pairs item)
              when (and pairs
                        (equal (mcp-json-lookup "type" pairs) "text"))
              do (let ((text (mcp-json-lookup "text" pairs)))
                   (when (stringp text)
                     (write-string text out))))))))

(defun parse-mcp-response (json)
  "Parse MCP JSON-RPC response, return (error . content) cons.
   Uses Kestrel json-parser for robust JSON handling."
  (if (not (stringp json))
      (cons "Invalid response: not a string" "")
    (multiple-value-bind (err parsed)
        (parse-string-as-json json)
      (if err
          (cons (format nil "JSON parse error: ~a" err) "")
        (let* ((pairs (mcp-json-get-object-pairs parsed))
               (error-val (mcp-json-lookup "error" pairs))
               (result-val (mcp-json-lookup "result" pairs)))
          (cond
           ;; JSON-RPC error object
           ((and error-val (consp error-val) (eq (car error-val) :object))
            (let* ((error-pairs (mcp-json-get-object-pairs error-val))
                   (msg (mcp-json-lookup "message" error-pairs)))
              (cons (if (stringp msg) msg "Unknown MCP error") "")))
           ;; Success - extract content from result object
           ((and result-val (consp result-val) (eq (car result-val) :object))
            (let* ((result-pairs (mcp-json-get-object-pairs result-val))
                   (content-val (mcp-json-lookup "content" result-pairs))
                   (text (mcp-extract-text-content content-val)))
              (cons nil (if (stringp text) text ""))))
           ;; No result or error - might be direct text
           (t
            (cons "MCP response missing result and error" ""))))))))
