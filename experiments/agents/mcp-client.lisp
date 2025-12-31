; MCP Client -- HTTP client for Model Context Protocol
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance
;
; This book provides an MCP client for calling tools on an MCP server
; via HTTP (using mcp-proxy or similar HTTP wrapper).
; Uses the same oracle-based pattern as llm-client.lisp.
;
; DESIGN: The MCP connection encapsulates both:
;   1. MCP transport session (Mcp-Session-Id header for HTTP transport)
;   2. ACL2 persistent session (for fast code execution without banner)
;
; The agent logic sees only an opaque mcp-connection - no session IDs exposed.
; To use multiple ACL2 sessions, create multiple mcp-connections.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "http-json" 
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json)))
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/explode-nonnegative-integer" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Configuration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Default MCP server endpoint (mcp-proxy or uvx mcp-server-http)
(defconst *mcp-default-endpoint* 
  "http://localhost:8000/mcp")

(defconst *mcp-connect-timeout* 10)   ; seconds
(defconst *mcp-read-timeout* 60)      ; seconds (higher for ACL2 operations)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MCP Connection Type (FTY)
;;
;; An MCP connection encapsulates:
;;   - endpoint: URL of the MCP server
;;   - transport-session-id: MCP protocol session (Mcp-Session-Id header)
;;   - acl2-session-id: Persistent ACL2 process session (for fast execution)
;;
;; Agent code treats this as opaque. Multiple connections = multiple sessions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod mcp-connection
  ((endpoint stringp :default "")
   (transport-session-id stringp :default "")
   (acl2-session-id stringp :default ""))
  :tag :mcp-connection
  :layout :tree)

;; Predicate for valid connection (has non-empty endpoint and transport session)
(define mcp-connection-valid-p ((conn mcp-connection-p))
  :returns (valid booleanp)
  (and (not (equal (mcp-connection->endpoint conn) ""))
       (not (equal (mcp-connection->transport-session-id conn) ""))))

;; Check if connection has a persistent ACL2 session
(define mcp-connection-has-acl2-session-p ((conn mcp-connection-p))
  :returns (has-session booleanp)
  (not (equal (mcp-connection->acl2-session-id conn) "")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MCP Result Type
;;
;; MCP tool results contain either content or an error.
;; We use two separate string fields rather than maybe-stringp for simplicity.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod mcp-result
  ((has-error booleanp :default nil)
   (error stringp :default "")
   (content stringp :default ""))
  :tag :mcp-result
  :layout :tree)

;; Quick check for success
(define mcp-result-ok-p ((result mcp-result-p))
  :returns (ok booleanp)
  (not (mcp-result->has-error result)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON-RPC 2.0 Serialization Stubs
;;
;; These are replaced by raw Lisp implementations via include-raw.
;; MCP uses JSON-RPC 2.0 format:
;; Request:  {"jsonrpc":"2.0","method":"tools/call","params":{...},"id":1}
;; Response: {"jsonrpc":"2.0","result":{...},"id":1} 
;;       or: {"jsonrpc":"2.0","error":{"code":...,"message":...},"id":1}
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize MCP tool call request to JSON-RPC 2.0
(defun serialize-mcp-tool-call (tool-name args-json request-id)
  (declare (xargs :guard (and (stringp tool-name)
                              (stringp args-json)
                              (natp request-id)))
           (ignore tool-name args-json request-id))
  (prog2$ (er hard? 'serialize-mcp-tool-call "Raw Lisp definition not installed?")
          "{}"))

(defthm stringp-of-serialize-mcp-tool-call
  (stringp (serialize-mcp-tool-call tool-name args-json request-id)))

;; Parse MCP JSON-RPC response, extract result content or error
;; Returns (cons error-or-nil content-string)
(defun parse-mcp-response-raw (json)
  (declare (xargs :guard (stringp json))
           (ignore json))
  (prog2$ (er hard? 'parse-mcp-response-raw "Raw Lisp definition not installed?")
          (cons "Raw Lisp not loaded" "")))

(defthm consp-of-parse-mcp-response-raw
  (consp (parse-mcp-response-raw json)))

;; Wrapper that returns mcp-result
(define parse-mcp-response ((json stringp))
  :returns (result mcp-result-p)
  (b* ((raw (parse-mcp-response-raw json))
       (err (car raw))
       (content (if (stringp (cdr raw)) (cdr raw) "")))
    (make-mcp-result :has-error (if (stringp err) t nil)
                     :error (if (stringp err) err "")
                     :content content)))

;; Serialize MCP initialize request to JSON-RPC 2.0
(defun serialize-mcp-initialize (request-id)
  (declare (xargs :guard (natp request-id))
           (ignore request-id))
  (prog2$ (er hard? 'serialize-mcp-initialize "Raw Lisp definition not installed?")
          "{}"))

(defthm stringp-of-serialize-mcp-initialize
  (stringp (serialize-mcp-initialize request-id)))

;; Parse MCP session ID from response headers alist
;; Returns session-id string or nil
(defun parse-mcp-session-id (headers-alist)
  (declare (xargs :guard (alistp headers-alist))
           (ignore headers-alist))
  (prog2$ (er hard? 'parse-mcp-session-id "Raw Lisp definition not installed?")
          nil))

(defthm stringp-or-null-of-parse-mcp-session-id
  (or (null (parse-mcp-session-id headers))
      (stringp (parse-mcp-session-id headers)))
  :rule-classes (:rewrite :type-prescription))

;; Build JSON object from key-value pairs (all string values)
(defun serialize-string-args (pairs)
  (declare (xargs :guard (alistp pairs))
           (ignore pairs))
  (prog2$ (er hard? 'serialize-string-args "Raw Lisp definition not installed?")
          "{}"))

(defthm stringp-of-serialize-string-args
  (stringp (serialize-string-args pairs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trust tag and raw Lisp inclusion
;;
;; IMPORTANT: This MUST come before any functions that call the raw Lisp
;; implementations, otherwise compiled code uses logical stubs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :mcp-client)

(include-raw "mcp-client-raw.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper to check if HTTP status indicates success (2xx)
(define mcp-http-success-p ((status natp))
  :returns (success booleanp)
  (and (>= status 200)
       (< status 300)))

;; Global request ID counter
(defconst *mcp-request-id* 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal: MCP Transport Connection
;;
;; Establishes MCP transport session only (gets Mcp-Session-Id header).
;; Called by mcp-connect before starting ACL2 session.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-transport-connect (endpoint state)
  "Establish MCP transport session. Returns (mv err transport-session-id state)."
  (declare (xargs :guard (stringp endpoint)
                  :stobjs state
                  :mode :program))
  (b* ((request-json (serialize-mcp-initialize 1))
       (headers '(("Content-Type" . "application/json")
                  ("Accept" . "application/json, text/event-stream")))
       
       ((mv http-err body status-raw response-headers state)
        (post-json-with-headers endpoint request-json headers 
                                *mcp-connect-timeout* *mcp-read-timeout* state))
       
       (status (nfix status-raw))
       
       ((when http-err)
        (mv (str::cat "MCP transport HTTP error: " http-err) "" state))
       
       ((unless (mcp-http-success-p status))
        (mv (concatenate 'string "MCP transport HTTP status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string)
                        ": " body) 
            "" state))
       
       (session-id (parse-mcp-session-id response-headers))
       
       ((unless session-id)
        (mv "MCP transport: no Mcp-Session-Id in response headers" "" state)))
    
    (mv nil session-id state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal: Raw Tool Call
;;
;; Low-level tool call using transport session ID directly.
;; Used internally by mcp-connect to start ACL2 session.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-call-tool-raw (endpoint transport-session-id tool-name args state)
  "Call MCP tool using raw transport session. Returns (mv err content state)."
  (declare (xargs :guard (and (stringp endpoint)
                              (stringp transport-session-id)
                              (stringp tool-name)
                              (alistp args))
                  :stobjs state
                  :mode :program))
  (b* ((args-json (serialize-string-args args))
       (request-json (serialize-mcp-tool-call tool-name args-json *mcp-request-id*))
       (headers (list (cons "Content-Type" "application/json")
                      (cons "Accept" "application/json")
                      (cons "Mcp-Session-Id" transport-session-id)))
       
       ((mv http-err body status-raw state)
        (post-json endpoint request-json headers 
                   *mcp-connect-timeout* *mcp-read-timeout* state))
       
       (status (nfix status-raw))
       
       ((when http-err)
        (mv (str::cat "MCP HTTP error: " http-err) "" state))
       
       ((unless (mcp-http-success-p status))
        (mv (concatenate 'string "MCP HTTP status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string)
                        ": " body) 
            "" state))
       
       (result (parse-mcp-response body)))
    
    (mv (if (mcp-result->has-error result)
            (mcp-result->error result)
          nil)
        (mcp-result->content result)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main API: mcp-connect
;;
;; Creates an MCP connection with:
;;   1. MCP transport session (for HTTP protocol)
;;   2. Persistent ACL2 session (for fast code execution)
;;
;; The agent just gets an opaque connection object.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-connect (endpoint state)
  "Connect to MCP server, establish transport and ACL2 sessions.
   Returns (mv err connection state) where connection is mcp-connection-p."
  (declare (xargs :guard (stringp endpoint)
                  :stobjs state
                  :mode :program))
  (b* (;; Step 1: Establish MCP transport session
       ((mv transport-err transport-session-id state)
        (mcp-transport-connect endpoint state))
       
       ((when transport-err)
        (mv transport-err nil state))
       
       ;; Step 2: Start persistent ACL2 session
       ((mv acl2-err acl2-response state)
        (mcp-call-tool-raw endpoint transport-session-id "start_session"
                           (list (cons "name" "mcp-client-session"))
                           state))
       
       ;; Parse ACL2 session ID from response
       ;; Response format: "Session started successfully. ID: <uuid>"
       (acl2-session-id
        (if acl2-err
            ""  ; Fall back to one-shot mode if session start fails
          (b* ((id-pos (search "ID: " acl2-response))
               ((unless id-pos) "")
               (id-start (+ id-pos 4))
               ((unless (<= (+ id-start 36) (length acl2-response))) ""))
            (subseq acl2-response id-start (+ id-start 36)))))
       
       ;; Build connection object
       (conn (make-mcp-connection
              :endpoint endpoint
              :transport-session-id transport-session-id
              :acl2-session-id acl2-session-id)))
    
    (mv nil conn state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main API: Tool Calling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-call-tool (conn tool-name args state)
  "Call an MCP tool. Returns (mv err content state)."
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp tool-name)
                              (alistp args))
                  :stobjs state
                  :mode :program))
  (mcp-call-tool-raw (mcp-connection->endpoint conn)
                     (mcp-connection->transport-session-id conn)
                     tool-name
                     args
                     state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ACL2-MCP Convenience Functions
;;
;; These automatically use the persistent ACL2 session for fast execution.
;; The session ID is internal - agent code just passes the connection.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-acl2-evaluate (conn code state)
  "Evaluate ACL2 code. Uses persistent session if available."
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp code))
                  :stobjs state
                  :mode :program))
  (let* ((session-id (mcp-connection->acl2-session-id conn))
         (args (if (equal session-id "")
                   (list (cons "code" code))
                 (list (cons "code" code)
                       (cons "session_id" session-id)))))
    (mcp-call-tool conn "evaluate" args state)))

(defun mcp-acl2-admit (conn code state)
  "Test if ACL2 event would be admitted. Uses persistent session if available."
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp code))
                  :stobjs state
                  :mode :program))
  (let* ((session-id (mcp-connection->acl2-session-id conn))
         (args (if (equal session-id "")
                   (list (cons "code" code))
                 (list (cons "code" code)
                       (cons "session_id" session-id)))))
    (mcp-call-tool conn "admit" args state)))

(defun mcp-acl2-prove (conn code state)
  "Prove ACL2 theorem. Uses persistent session if available."
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp code))
                  :stobjs state
                  :mode :program))
  (let* ((session-id (mcp-connection->acl2-session-id conn))
         (args (if (equal session-id "")
                   (list (cons "code" code))
                 (list (cons "code" code)
                       (cons "session_id" session-id)))))
    (mcp-call-tool conn "prove" args state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Connection Management
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-disconnect (conn state)
  "Clean up MCP connection, ending ACL2 session if active."
  (declare (xargs :guard (mcp-connection-p conn)
                  :stobjs state
                  :mode :program))
  (let ((session-id (mcp-connection->acl2-session-id conn)))
    (if (equal session-id "")
        (mv nil "No ACL2 session to end" state)
      (mcp-call-tool conn "end_session"
                     (list (cons "session_id" session-id))
                     state))))

