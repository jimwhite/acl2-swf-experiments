; Test MCP Client -- Certifiable test book
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Certifiable test book for MCP client connection and tool calling.
; Requires mcp-proxy running:
;   mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --allow-origin='*' --pass-environment
;
; Certify with: cert.pl test-mcp-client.lisp

(in-package "ACL2")

(include-book "mcp-client" :ttags :all)
(include-book "std/util/bstar" :dir :system)

(defconst *test-endpoint* "http://localhost:8000/mcp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test Functions (program mode for I/O)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

;; Test 1: Connection establishment
(defun test-mcp-connect (endpoint state)
  (declare (xargs :stobjs state))
  (b* (((mv err conn state) (mcp-connect endpoint state))
       ((when err)
        (prog2$ (cw "FAIL test-mcp-connect: ~s0~%" err)
                (mv nil state))))
    (prog2$ (cw "PASS test-mcp-connect: session=~s0~%" 
                (mcp-connection-session-id conn))
            (mv conn state))))

;; Test 2: Evaluate simple expression
(defun test-mcp-evaluate (conn state)
  (declare (xargs :stobjs state))
  (b* (((mv err result state) (mcp-acl2-evaluate conn "(+ 1 2 3)" state))
       ((when err)
        (prog2$ (cw "FAIL test-mcp-evaluate: ~s0~%" err)
                (mv nil state))))
    (prog2$ (cw "PASS test-mcp-evaluate: (+ 1 2 3) => ~s0~%" result)
            (mv t state))))

;; Test 3: Admit a function definition
(defun test-mcp-admit (conn state)
  (declare (xargs :stobjs state))
  (b* (((mv err result state) 
        (mcp-acl2-admit conn "(defun mcp-test-fn (x) (+ x 1))" state))
       ((when err)
        (prog2$ (cw "FAIL test-mcp-admit: ~s0~%" err)
                (mv nil state)))
       ;; Truncate long output for display
       (display (if (> (length result) 100)
                    (concatenate 'string (subseq result 0 100) "...")
                    result)))
    (prog2$ (cw "PASS test-mcp-admit: ~s0~%" display)
            (mv t state))))

;; Test 4: Prove a simple theorem
(defun test-mcp-prove (conn state)
  (declare (xargs :stobjs state))
  (b* (((mv err result state)
        (mcp-acl2-prove conn "(defthm mcp-test-thm (equal (+ 1 1) 2))" state))
       ((when err)
        (prog2$ (cw "FAIL test-mcp-prove: ~s0~%" err)
                (mv nil state)))
       (display (if (> (length result) 100)
                    (concatenate 'string (subseq result 0 100) "...")
                    result)))
    (prog2$ (cw "PASS test-mcp-prove: ~s0~%" display)
            (mv t state))))

;; Test 5: List ACL2 sessions
(defun test-mcp-list-sessions (conn state)
  (declare (xargs :stobjs state))
  (b* (((mv err result state) (mcp-call-tool conn "list_sessions" nil state))
       ((when err)
        (prog2$ (cw "FAIL test-mcp-list-sessions: ~s0~%" err)
                (mv nil state))))
    (prog2$ (cw "PASS test-mcp-list-sessions: ~s0~%" result)
            (mv t state))))

;; Run all tests
(defun run-mcp-client-tests (state)
  (declare (xargs :stobjs state))
  (b* ((endpoint *test-endpoint*)
       (- (cw "~%===== MCP Client Tests =====~%"))
       (- (cw "Endpoint: ~s0~%~%" endpoint))
       
       ;; Test connection
       ((mv conn state) (test-mcp-connect endpoint state))
       ((when (null conn))
        (prog2$ (cw "~%ABORT: Connection failed, cannot continue tests~%")
                (mv nil state)))
       
       ;; Test evaluate
       ((mv ok state) (test-mcp-evaluate conn state))
       ((when (null ok))
        (mv nil state))
       
       ;; Test admit
       ((mv ok state) (test-mcp-admit conn state))
       ((when (null ok))
        (mv nil state))
       
       ;; Test prove
       ((mv ok state) (test-mcp-prove conn state))
       ((when (null ok))
        (mv nil state))
       
       ;; Test list sessions
       ((mv ok state) (test-mcp-list-sessions conn state))
       ((when (null ok))
        (mv nil state))
       
       (- (cw "~%===== All tests passed! =====~%")))
    (mv t state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integration tests - run manually, not during certification
;;
;; To run tests after certification:
;;   1. Start mcp-proxy: mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --allow-origin='*' --pass-environment
;;   2. In ACL2: (include-book "test-mcp-client" :ttags :all)
;;   3. Run: (run-mcp-client-tests state)
;;
;; Or use curl directly:
;;   curl -X POST http://localhost:8000/mcp -H "Content-Type: application/json" \
;;     -d '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"evaluate","arguments":{"code":"(+ 1 2)"}},"id":1}'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests are NOT run during certification - this just certifies that the
;; test functions are well-formed. Run manually after certification.
