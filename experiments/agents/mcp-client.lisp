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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "http-json" 
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json)))
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/explode-nonnegative-integer" :dir :system)
(include-book "std/util/bstar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Configuration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Default MCP server endpoint (mcp-proxy or uvx mcp-server-http)
;; User can override with mcp-call-tool's endpoint parameter
(defconst *mcp-default-endpoint* 
  "http://localhost:8000/mcp")

(defconst *mcp-connect-timeout* 10)   ; seconds
(defconst *mcp-read-timeout* 60)      ; seconds (higher for ACL2 operations)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MCP Connection Type
;;
;; An MCP connection holds the endpoint URL and session ID.
;; The session ID is obtained from the initialize handshake.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; MCP connection: (endpoint . mcp-session-id)
;; Both are strings; mcp-session-id obtained from initialize response header

(defun mcp-connection-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (stringp (car x))   ; endpoint URL
       (stringp (cdr x)))) ; mcp-session-id

(defun mcp-connection-endpoint (conn)
  (declare (xargs :guard (mcp-connection-p conn)))
  (car conn))

(defun mcp-connection-session-id (conn)
  (declare (xargs :guard (mcp-connection-p conn)))
  (cdr conn))

(defun make-mcp-connection (endpoint session-id)
  (declare (xargs :guard (and (stringp endpoint)
                              (stringp session-id))))
  (cons endpoint session-id))

(defthm mcp-connection-p-of-make-mcp-connection
  (implies (and (stringp endpoint)
                (stringp session-id))
           (mcp-connection-p (make-mcp-connection endpoint session-id))))

(defthm stringp-of-mcp-connection-endpoint
  (implies (mcp-connection-p conn)
           (stringp (mcp-connection-endpoint conn))))

(defthm stringp-of-mcp-connection-session-id
  (implies (mcp-connection-p conn)
           (stringp (mcp-connection-session-id conn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MCP Result Type
;;
;; MCP tool results contain either content or an error.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple result representation: (error-string . content-string)
;; error-string is nil on success, content-string is the tool output

(defun mcp-result-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (or (null (car x)) (stringp (car x)))  ; error or nil
       (stringp (cdr x))))                     ; content

(defun mcp-result-error (result)
  (declare (xargs :guard (mcp-result-p result)))
  (car result))

(defun mcp-result-content (result)
  (declare (xargs :guard (mcp-result-p result)))
  (cdr result))

(defun make-mcp-result (error content)
  (declare (xargs :guard (and (or (null error) (stringp error))
                              (stringp content))))
  (cons error content))

(defthm mcp-result-p-of-make-mcp-result
  (implies (and (or (null error) (stringp error))
                (stringp content))
           (mcp-result-p (make-mcp-result error content))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON-RPC 2.0 Serialization
;;
;; MCP uses JSON-RPC 2.0 format:
;; Request:  {"jsonrpc":"2.0","method":"tools/call","params":{...},"id":1}
;; Response: {"jsonrpc":"2.0","result":{...},"id":1} 
;;       or: {"jsonrpc":"2.0","error":{"code":...,"message":...},"id":1}
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serialize MCP tool call request to JSON-RPC 2.0
;; tool-name: string, tool arguments as JSON object string
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
;; Returns mcp-result-p: (error . content)
(defun parse-mcp-response (json)
  (declare (xargs :guard (stringp json))
           (ignore json))
  (prog2$ (er hard? 'parse-mcp-response "Raw Lisp definition not installed?")
          (make-mcp-result "Raw Lisp not loaded" "")))

(defthm mcp-result-p-of-parse-mcp-response
  (mcp-result-p (parse-mcp-response json)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MCP Initialize Serialization
;;
;; JSON-RPC 2.0 initialize request for MCP transport session
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Convenience: Serialize simple tool arguments
;;
;; For tools with simple string arguments, build JSON object
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Build JSON object from key-value pairs (all string values)
;; Input: list of (key . value) pairs where both are strings
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
;; implementations (like mcp-connect), otherwise the compiled code will
;; use the logical stub definitions instead of the raw Lisp implementations.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :mcp-client)

(include-raw "mcp-client-raw.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main API Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper to check if HTTP status indicates success (2xx)
(defun mcp-http-success-p (status)
  (declare (xargs :guard (natp status)))
  (and (>= status 200)
       (< status 300)))

;; Global request ID counter (incremented per call)
;; For simplicity, we use a defconst; real impl could use state
(defconst *mcp-request-id* 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MCP Connection Establishment
;;
;; mcp-connect sends the initialize request and extracts the session ID
;; from the response headers. This session ID must be included in all
;; subsequent requests via the Mcp-Session-Id header.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mcp-connect (endpoint state)
  (declare (xargs :guard (stringp endpoint)
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (disable post-json-with-headers)))))
  (b* (;; Serialize the initialize request
       (request-json (serialize-mcp-initialize 1))
       (headers '(("Content-Type" . "application/json")
                  ("Accept" . "application/json, text/event-stream")))
       
       (- (cw "DEBUG mcp-connect: request=~s0~%" request-json))
       
       ;; Make HTTP POST request with headers
       ((mv http-err body status-raw response-headers state)
        (post-json-with-headers endpoint request-json headers 
                                *mcp-connect-timeout* *mcp-read-timeout* state))
       
       (- (cw "DEBUG mcp-connect: http-err=~x0 status=~x1~%" http-err status-raw))
       (- (cw "DEBUG mcp-connect: response-headers=~x0~%" response-headers))
       
       ;; Coerce status to natp for guard
       (status (mbe :logic (nfix status-raw) :exec status-raw))
       
       ;; Check for HTTP error
       ((when http-err)
        (mv (str::cat "MCP connect HTTP error: " http-err) nil state))
       
       ;; Check for non-2xx status
       ((unless (mcp-http-success-p status))
        (mv (concatenate 'string "MCP connect HTTP status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string)
                        ": " body) 
            nil state))
       
       ;; Extract session ID from response headers
       (session-id (parse-mcp-session-id response-headers))
       (- (cw "DEBUG mcp-connect: parsed session-id=~x0~%" session-id))
       
       ;; Check we got a session ID
       ((unless session-id)
        (mv "MCP connect: no Mcp-Session-Id in response headers" nil state)))
    
    ;; Success: return connection
    (mv nil (make-mcp-connection endpoint session-id) state)))

;; Return type theorems for mcp-connect
(defthm mcp-connection-p-of-mcp-connect
  (implies (mv-nth 1 (mcp-connect endpoint state))
           (mcp-connection-p (mv-nth 1 (mcp-connect endpoint state)))))

(defthm state-p1-of-mcp-connect
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (mcp-connect endpoint state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main API - Tool Calling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Call an MCP tool via HTTP using a connection
;;
;; Parameters:
;;   conn      - MCP connection from mcp-connect (mcp-connection-p)
;;   tool-name - Name of the tool to call (stringp)  
;;   args-json - Tool arguments as JSON object string (stringp)
;;   state     - ACL2 state
;;
;; Returns: (mv error content state)
;;   error   - NIL on success, error string on failure
;;   content - Tool result content (stringp, empty on error)
;;   state   - Updated state
(defun mcp-call-tool-with-json (conn tool-name args-json state)
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp tool-name)
                              (stringp args-json))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (disable post-json)))))
  (b* (;; Extract connection details
       (endpoint (mcp-connection-endpoint conn))
       (session-id (mcp-connection-session-id conn))
       
       ;; Serialize the request to JSON-RPC 2.0 format
       (request-json (serialize-mcp-tool-call tool-name args-json *mcp-request-id*))
       ;; Include session ID and Accept headers
       (headers (list (cons "Content-Type" "application/json")
                      (cons "Accept" "application/json")
                      (cons "Mcp-Session-Id" session-id)))
       
       ;; Make HTTP POST request
       ((mv http-err body status-raw state)
        (post-json endpoint request-json headers 
                   *mcp-connect-timeout* *mcp-read-timeout* state))
       
       ;; Coerce status to natp (it is, via theorem, but help guard verification)
       (status (mbe :logic (nfix status-raw) :exec status-raw))
       
       ;; Check for HTTP error
       ((when http-err)
        (mv (str::cat "MCP HTTP error: " http-err) "" state))
       
       ;; Check for non-2xx status
       ((unless (mcp-http-success-p status))
        (mv (concatenate 'string "MCP HTTP status " 
                        (coerce (explode-nonnegative-integer status 10 nil) 'string)
                        ": " body) 
            "" state))
       
       ;; Parse JSON-RPC response
       (result (parse-mcp-response body)))
    
    (mv (mcp-result-error result)
        (mcp-result-content result)
        state)))

;; Return type theorems
(defthm stringp-of-mcp-call-tool-with-json-content
  (stringp (mv-nth 1 (mcp-call-tool-with-json conn tool-name args-json state))))

(defthm state-p1-of-mcp-call-tool-with-json
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (mcp-call-tool-with-json conn tool-name args-json state)))))

;; Convenience: Call MCP tool with string key-value arguments
;;
;; Parameters:
;;   conn      - MCP connection from mcp-connect
;;   tool-name - Name of the tool
;;   args      - Alist of (string-key . string-value) pairs
;;   state     - ACL2 state
;;
;; Returns: (mv error content state)
(defun mcp-call-tool (conn tool-name args state)
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp tool-name)
                              (alistp args))
                  :stobjs state))
  (let ((args-json (serialize-string-args args)))
    (mcp-call-tool-with-json conn tool-name args-json state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ACL2-MCP Specific Convenience Functions
;;
;; These wrap common acl2-mcp tool calls for verified agent use.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Evaluate ACL2 code via acl2-mcp
;;
;; Parameters:
;;   conn  - MCP connection from mcp-connect
;;   code  - ACL2 code to evaluate (stringp)
;;   state - ACL2 state
;;
;; Returns: (mv error result state)
(defun mcp-acl2-evaluate (conn code state)
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp code))
                  :stobjs state))
  (mcp-call-tool conn "evaluate" 
                 (list (cons "code" code))
                 state))

;; Admit ACL2 event (test without saving)
;;
;; Parameters:
;;   conn  - MCP connection from mcp-connect
;;   code  - ACL2 event to test (stringp)
;;   state - ACL2 state
;;
;; Returns: (mv error result state)
(defun mcp-acl2-admit (conn code state)
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp code))
                  :stobjs state))
  (mcp-call-tool conn "admit"
                 (list (cons "code" code))
                 state))

;; Prove ACL2 theorem
;;
;; Parameters:
;;   conn  - MCP connection from mcp-connect
;;   code  - defthm form to prove (stringp)
;;   state - ACL2 state
;;
;; Returns: (mv error result state)
(defun mcp-acl2-prove (conn code state)
  (declare (xargs :guard (and (mcp-connection-p conn)
                              (stringp code))
                  :stobjs state))
  (mcp-call-tool conn "prove"
                 (list (cons "code" code))
                 state))
