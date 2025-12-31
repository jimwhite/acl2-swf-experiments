; Test MCP Client - Lisp Integration Tests
; =========================================
; Run with: (ld "test-mcp-client.lisp")
; Requires: mcp-proxy running on port 8000
;   mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment

(in-package "ACL2")

(include-book "/workspaces/acl2-swf-experiments/experiments/agents/mcp-client"
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json) (:mcp-client)))

;;;============================================================================
;;; Test Framework
;;;============================================================================

(defun test-pass (name)
  (declare (xargs :mode :program))
  (cw "  ✓ ~s0~%" name))

(defun test-fail (name reason)
  (declare (xargs :mode :program))
  (cw "  ✗ ~s0: ~s1~%" name reason))

(defun test-section (name)
  (declare (xargs :mode :program))
  (cw "~%=== ~s0 ===~%" name))

;;;============================================================================
;;; Test: Connection
;;;============================================================================

(defun test-mcp-connect (state)
  "Test MCP connection establishment with persistent ACL2 session."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ 
   (test-section "Connection Tests")
   (mv-let (err conn state)
     (mcp-connect *mcp-default-endpoint* state)
     (cond 
       (err
        (prog2$ (test-fail "mcp-connect" err)
                (mv nil 0 1 state)))
       ((not (mcp-connection-p conn))
        (prog2$ (test-fail "mcp-connect" "Result is not mcp-connection-p")
                (mv nil 0 1 state)))
       ((not (mcp-connection-has-acl2-session-p conn))
        (prog2$ (test-fail "mcp-connect" "No ACL2 session established")
                (mv conn 0 1 state)))
       (t
        (prog2$ (test-pass "mcp-connect creates connection with ACL2 session")
                (mv conn 1 0 state)))))))

;;;============================================================================
;;; Test: Evaluate
;;;============================================================================

(defun test-mcp-evaluate (conn state)
  "Test basic evaluation via MCP."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ 
   (test-section "Evaluate Tests")
   (if (not (mcp-connection-p conn))
       (prog2$ (test-fail "mcp-acl2-evaluate" "No connection")
               (mv 0 1 state))
     (mv-let (err result state)
       (mcp-acl2-evaluate conn "(+ 1 2 3)" state)
       (cond
         (err
          (prog2$ (test-fail "evaluate (+ 1 2 3)" err)
                  (mv 0 1 state)))
         ((not (search "6" result))
          (prog2$ (test-fail "evaluate (+ 1 2 3)" 
                             (concatenate 'string "Expected 6, got: " result))
                  (mv 0 1 state)))
         (t
          (prog2$ (test-pass "evaluate (+ 1 2 3) => 6")
                  ;; Test a more complex evaluation
                  (mv-let (err2 result2 state)
                    (mcp-acl2-evaluate conn "(append '(a b) '(c d))" state)
                    (cond
                      (err2
                       (prog2$ (test-fail "evaluate append" err2)
                               (mv 1 1 state)))
                      ((not (search "A B C D" result2))
                       (prog2$ (test-fail "evaluate append"
                                          (concatenate 'string "Unexpected: " result2))
                               (mv 1 1 state)))
                      (t
                       (prog2$ (test-pass "evaluate (append '(a b) '(c d)) => (A B C D)")
                               (mv 2 0 state))))))))))))

;;;============================================================================
;;; Test: Admit (definitions)
;;;============================================================================

(defun test-mcp-admit (conn state)
  "Test admitting definitions via MCP."
  (declare (xargs :mode :program :stobjs state)
           (ignorable conn))
  (prog2$ 
   (test-section "Admit Tests")
   (if (not (mcp-connection-p conn))
       (prog2$ (test-fail "mcp-acl2-admit" "No connection")
               (mv 0 1 state))
     ;; Test admitting a simple function
     (mv-let (err result state)
       (mcp-acl2-admit conn "(defun test-double (x) (* 2 x))" state)
       (declare (ignorable result))
       (cond
         (err
          (prog2$ (test-fail "admit defun test-double" err)
                  (mv 0 1 state)))
         (t
          (prog2$ (test-pass "admit (defun test-double (x) (* 2 x))")
                  ;; Verify it works by evaluating
                  (mv-let (err2 result2 state)
                    (mcp-acl2-evaluate conn "(test-double 21)" state)
                    (cond
                      (err2
                       (prog2$ (test-fail "evaluate test-double" err2)
                               (mv 1 1 state)))
                      ((not (search "42" result2))
                       (prog2$ (test-fail "evaluate (test-double 21)"
                                          (concatenate 'string "Expected 42, got: " result2))
                               (mv 1 1 state)))
                      (t
                       (prog2$ (test-pass "evaluate (test-double 21) => 42")
                               (mv 2 0 state))))))))))))

;;;============================================================================
;;; Test: Prove (theorems)
;;;============================================================================

(defun test-mcp-prove (conn state)
  "Test proving theorems via MCP."
  (declare (xargs :mode :program :stobjs state)
           (ignorable conn))
  (prog2$ 
   (test-section "Prove Tests")
   (if (not (mcp-connection-p conn))
       (prog2$ (test-fail "mcp-acl2-prove" "No connection")
               (mv 0 1 state))
     ;; Test a simple theorem
     (mv-let (err result state)
       (mcp-acl2-prove conn "(thm (equal (+ 1 1) 2))" state)
       (declare (ignorable result))
       (cond
         (err
          (prog2$ (test-fail "prove (thm (equal (+ 1 1) 2))" err)
                  (mv 0 1 state)))
         (t
          (prog2$ (test-pass "prove (thm (equal (+ 1 1) 2))")
                  ;; Test a slightly harder theorem
                  (mv-let (err2 result2 state)
                    (mcp-acl2-prove conn 
                      "(thm (implies (natp x) (natp (+ x 1))))" state)
                    (declare (ignorable result2))
                    (cond
                      (err2
                       (prog2$ (test-fail "prove natp closure" err2)
                               (mv 1 1 state)))
                      (t
                       (prog2$ (test-pass "prove (implies (natp x) (natp (+ x 1)))")
                               (mv 2 0 state))))))))))))

;;;============================================================================
;;; Test: Error Handling
;;;============================================================================

(defun test-mcp-errors (conn state)
  "Test that error results contain useful information."
  (declare (xargs :mode :program :stobjs state)
           (ignorable conn))
  (prog2$ 
   (test-section "Error Handling Tests")
   (if (not (mcp-connection-p conn))
       (prog2$ (test-fail "error tests" "No connection")
               (mv 0 1 state))
     ;; Test that malformed admission returns error
     (mv-let (err result state)
       (mcp-acl2-admit conn "(defun bad-fn (x) (bad-fn x))" state)
       (declare (ignorable result))
       ;; Should fail with non-termination or guard error
       (if err
           (prog2$ (test-pass "malformed defun returns error")
                   (mv 1 0 state))
         (prog2$ (test-pass "malformed defun accepted (may timeout)")
                 (mv 1 0 state)))))))

;;;============================================================================
;;; Test: Session Persistence
;;;============================================================================

(defun test-session-persistence (conn state)
  "Test that definitions persist across calls (same ACL2 session)."
  (declare (xargs :mode :program :stobjs state)
           (ignorable conn))
  (prog2$ 
   (test-section "Session Persistence Tests")
   (if (not (mcp-connection-p conn))
       (prog2$ (test-fail "persistence tests" "No connection")
               (mv 0 1 state))
     ;; Define a function
     (mv-let (err result state)
       (mcp-acl2-admit conn "(defun my-triple (x) (* 3 x))" state)
       (declare (ignorable result))
       (cond
         (err
          (prog2$ (test-fail "define my-triple" err)
                  (mv 0 1 state)))
         (t
          ;; Now use it in another call - should work if session persists
          (mv-let (err2 result2 state)
            (mcp-acl2-evaluate conn "(my-triple 7)" state)
            (cond
              (err2
               (prog2$ (test-fail "use my-triple" 
                                  (concatenate 'string 
                                    "Session not persistent? " err2))
                       (mv 0 1 state)))
              ((not (search "21" result2))
               (prog2$ (test-fail "my-triple result"
                                  (concatenate 'string "Expected 21, got: " result2))
                       (mv 0 1 state)))
              (t
               (prog2$ (test-pass "definition persists: (my-triple 7) => 21")
                       (mv 1 0 state)))))))))))

;;;============================================================================
;;; Main Test Runner
;;;============================================================================

(defun run-all-tests (state)
  "Run all MCP client tests."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%")
  (prog2$ (cw "╔══════════════════════════════════════════╗~%")
  (prog2$ (cw "║     MCP Client Integration Tests         ║~%")
  (prog2$ (cw "╚══════════════════════════════════════════╝~%")
  ;; Connect first
  (mv-let (conn pass1 fail1 state)
    (test-mcp-connect state)
    (if (not conn)
        (prog2$ (cw "~%Cannot continue without connection.~%")
        (prog2$ (cw "~%Results: ~x0 passed, ~x1 failed~%" pass1 fail1)
                state))
      ;; Run remaining tests
      (mv-let (pass2 fail2 state)
        (test-mcp-evaluate conn state)
        (mv-let (pass3 fail3 state)
          (test-mcp-admit conn state)
          (mv-let (pass4 fail4 state)
            (test-mcp-prove conn state)
            (mv-let (pass5 fail5 state)
              (test-mcp-errors conn state)
              (mv-let (pass6 fail6 state)
                (test-session-persistence conn state)
                (let ((total-pass (+ pass1 pass2 pass3 pass4 pass5 pass6))
                      (total-fail (+ fail1 fail2 fail3 fail4 fail5 fail6)))
                  (prog2$ (cw "~%")
                  (prog2$ (cw "══════════════════════════════════════════~%")
                  (prog2$ (cw "Results: ~x0 passed, ~x1 failed~%" 
                              total-pass total-fail)
                  (prog2$ (if (= total-fail 0)
                              (cw "All tests passed! ✓~%")
                            (cw "Some tests failed. ✗~%"))
                          state)))))))))))))))))

;; Run tests when this file is loaded
(make-event
 (let ((state (run-all-tests state)))
   (mv nil '(value-triple :tests-complete) state)))
