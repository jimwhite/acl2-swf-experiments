; Test MCP Client -- Interactive tests for mcp-client.lisp
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; This file contains interactive tests for the MCP client.
; Run with mcp-proxy running on port 8000:
;   mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --allow-origin='*' --pass-environment
;
; Then load this file in ACL2:
;   (ld "test-mcp-client.lisp")

(in-package "ACL2")

;; Load the MCP client
(include-book "mcp-client" :ttags :all)

(defconst *test-endpoint* "http://localhost:8000/mcp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Individual Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test: Connect to mcp-proxy and call evaluate
(defun test-mcp-client (state)
  (declare (xargs :stobjs state :mode :program)
           (ignorable state))
  (b* ((endpoint *test-endpoint*)
       
       ;; Connect (sends initialize, gets session ID)
       ((mv err conn state) (mcp-connect endpoint state))
       ((when err)
        (prog2$ (cw "~%Connection error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Connected! Session: ~s0~%" (mcp-connection-session-id conn)))
       
       ;; Test evaluate tool
       ((mv err result state) (mcp-acl2-evaluate conn "(+ 1 2 3)" state))
       ((when err)
        (prog2$ (cw "~%Evaluate error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Evaluate (+ 1 2 3) = ~s0~%" result))
       
       ;; Test admit tool
       ((mv err result state) (mcp-acl2-admit conn "(defun my-test-fn (x) (+ x 1))" state))
       ((when err)
        (prog2$ (cw "~%Admit error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Admit result: ~s0~%" (if (> (length result) 200)
                                          (concatenate 'string (subseq result 0 200) "...")
                                          result))))
    
    (mv t state)))

;; Test: Prove a simple theorem
(defun test-mcp-prove (state)
  (declare (xargs :stobjs state :mode :program)
           (ignorable state))
  (b* (((mv err conn state) (mcp-connect *test-endpoint* state))
       ((when err)
        (prog2$ (cw "~%Connection error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Testing prove...~%"))
       
       ((mv err result state) 
        (mcp-acl2-prove conn "(defthm natp-plus (implies (and (natp x) (natp y)) (natp (+ x y))))" state))
       ((when err)
        (prog2$ (cw "~%Prove error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Prove result (~x0 chars): ~s1~%" 
              (length result)
              (if (> (length result) 300)
                  (concatenate 'string (subseq result 0 300) "...")
                  result))))
    (mv t state)))

;; Test: List ACL2 sessions
(defun test-mcp-list-sessions (state)
  (declare (xargs :stobjs state :mode :program)
           (ignorable state))
  (b* (((mv err conn state) (mcp-connect *test-endpoint* state))
       ((when err)
        (prog2$ (cw "~%Connection error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Listing ACL2 sessions...~%"))
       
       ((mv err result state) (mcp-call-tool conn "list_sessions" nil state))
       ((when err)
        (prog2$ (cw "~%list_sessions error: ~s0~%" err)
                (mv nil state)))
       
       (- (cw "~%Sessions: ~s0~%" result)))
    (mv t state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Run all tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun run-all-mcp-tests (state)
  (declare (xargs :stobjs state :mode :program)
           (ignorable state))
  (prog2$ (cw "~%========================================~%")
  (prog2$ (cw "MCP Client Tests~%")
  (prog2$ (cw "Endpoint: ~s0~%" *test-endpoint*)
  (prog2$ (cw "========================================~%")
  (b* (((mv ok1 state) (test-mcp-client state))
       (- (cw "~%--- test-mcp-client: ~s0 ---~%" (if ok1 "PASS" "FAIL")))
       
       ((mv ok2 state) (test-mcp-prove state))
       (- (cw "~%--- test-mcp-prove: ~s0 ---~%" (if ok2 "PASS" "FAIL")))
       
       ((mv ok3 state) (test-mcp-list-sessions state))
       (- (cw "~%--- test-mcp-list-sessions: ~s0 ---~%" (if ok3 "PASS" "FAIL"))))
    
    (prog2$ (cw "~%========================================~%")
    (prog2$ (cw "Tests complete: ~x0/3 passed~%" (+ (if ok1 1 0) (if ok2 1 0) (if ok3 1 0)))
    (prog2$ (cw "========================================~%")
            (mv (and ok1 ok2 ok3) state))))))))))

;; Print usage on load
(cw "~%MCP Client Test file loaded.~%")
(cw "~%To run tests:~%")
(cw "  (test-mcp-client state)      ; Basic connect + evaluate + admit~%")
(cw "  (test-mcp-prove state)       ; Test theorem proving~%")
(cw "  (test-mcp-list-sessions state) ; List ACL2 sessions~%")
(cw "  (run-all-mcp-tests state)    ; Run all tests~%")
(cw "~%Make sure mcp-proxy is running:~%")
(cw "  mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --allow-origin='*' --pass-environment~%~%")
