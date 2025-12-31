; Test MCP Persistent Session
; ============================
; This file tests that the MCP client properly creates and reuses
; a persistent ACL2 session. The key test is that a function defined
; in one call can be used in a subsequent call (proving state persists).
;
; Usage:
;   cd /workspaces/acl2-swf-experiments/experiments/agents
;   acl2
;   (ld "test-mcp-session.lisp")
;
; Prerequisites:
;   - acl2-mcp server running: cd acl2-mcp && uv run acl2-mcp
;   - Server listens on http://localhost:8000

(in-package "ACL2")

;; Load the MCP client
(ld "mcp-client.lisp")

;; Test persistent session
(make-event 
  (mv-let (err conn state)
    (mcp-connect "http://localhost:8000" state)
    (if err
        (prog2$ (cw "~%=== CONNECTION FAILED ===~%")
          (prog2$ (cw "Error: ~s0~%" err)
            (prog2$ (cw "~%Make sure acl2-mcp server is running:~%")
              (prog2$ (cw "  cd acl2-mcp && uv run acl2-mcp~%")
                (value `(value-triple :connection-error))))))
      (prog2$ (cw "~%=== MCP SESSION TEST ===~%")
        (prog2$ (cw "Transport Session: ~s0~%" (mcp-connection->transport-session-id conn))
          (prog2$ (cw "ACL2 Session: ~s0~%" (mcp-connection->acl2-session-id conn))
            (prog2$ (cw "~%--- Test 1: Simple eval ---~%")
              (mv-let (err1 result1 state)
                (mcp-acl2-evaluate conn "(+ 1 2 3)" state)
                (prog2$ (cw "Code: (+ 1 2 3)~%")
                  (prog2$ (cw "Result: ~s0~%" (if err1 (concatenate 'string "ERROR: " err1) result1))
                    (prog2$ (cw "~%--- Test 2: Define function ---~%")
                      (mv-let (err2 result2 state)
                        (mcp-acl2-evaluate conn "(defun my-triple (x) (* x 3))" state)
                        (prog2$ (cw "Code: (defun my-triple (x) (* x 3))~%")
                          (prog2$ (cw "Result: ~s0~%" 
                                      (if err2 
                                          (concatenate 'string "ERROR: " err2) 
                                          (subseq result2 0 (min 60 (length result2)))))
                            (prog2$ (cw "~%--- Test 3: Use defined function ---~%")
                              (mv-let (err3 result3 state)
                                (mcp-acl2-evaluate conn "(my-triple 14)" state)
                                (prog2$ (cw "Code: (my-triple 14)~%")
                                  (prog2$ (cw "Result: ~s0~%" (if err3 (concatenate 'string "ERROR: " err3) result3))
                                    (prog2$ (cw "Expected: 42~%")
                                      (prog2$ (cw "~%--- Cleanup ---~%")
                                        (mv-let (derr dresult state)
                                          (mcp-disconnect conn state)
                                          (declare (ignore dresult))
                                          (prog2$ (cw "Disconnect: ~s0~%" (if derr "failed" "ok"))
                                            (prog2$ (cw "~%=== TEST COMPLETE ===~%")
                                              (if (and (not err1) (not err2) (not err3)
                                                       (search "42" result3))
                                                  (prog2$ (cw "STATUS: PASS - Session persistence verified!~%")
                                                    (value `(value-triple :pass)))
                                                (prog2$ (cw "STATUS: FAIL - Check errors above~%")
                                                  (value `(value-triple :fail)))))))))))))))))))))))))))

;; Exit after test
:q
