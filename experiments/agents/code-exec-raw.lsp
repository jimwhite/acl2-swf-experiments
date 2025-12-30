; code-exec-raw.lsp - Raw Lisp Bridge for Safe ACL2 Code Execution
;
; This file provides the actual code execution functionality using
; acl2s-compute from acl2s-interface. It must be loaded with include-raw.
;
; The key pattern (like mini-swe-agent's bash execution):
; 1. Parse code string with safety checks
; 2. Execute via acl2s-compute (which catches errors)
; 3. Format result for LLM consumption
;
; Safety model:
; - *read-eval* set to nil to prevent #. reader macro
; - Forbidden symbol checking before execution
; - All errors caught and converted to error messages
; - No state mutation escapes the sandbox

(in-package "ACL2")

;;;============================================================================
;;; Security Checking
;;;============================================================================

;; List of forbidden symbols (must match code-exec.lisp)
(defparameter *forbidden-symbols-raw*
  '(sys-call sys-call-status sys-call+
    set-raw-mode set-raw-mode-on set-raw-mode-on!
    progn! with-raw-mode
    defttag 
    remove-untouchable push-untouchable
    open-input-channel open-output-channel
    read-file-into-string
    assign f-put-global
    include-book ld load include-raw
    defpkg in-package))

;; Check if a symbol is forbidden
(defun forbidden-symbol-p-raw (sym)
  (and (symbolp sym)
       (member sym *forbidden-symbols-raw* :test #'eq)))

;; Recursively check if form contains forbidden symbols
(defun code-safe-p-raw (form)
  (cond
   ((null form) t)
   ((atom form) (not (forbidden-symbol-p-raw form)))
   (t (and (code-safe-p-raw (car form))
           (code-safe-p-raw (cdr form))))))

;;;============================================================================
;;; Result Formatting
;;;============================================================================

;; Format value for LLM output
(defun format-value-for-llm (value)
  (let ((*print-length* 100)    ; Limit list printing
        (*print-level* 5)       ; Limit nesting depth
        (*print-pretty* t))     ; Pretty print
    (format nil "~S" value)))

;; Format the complete result
(defun format-exec-result (err-flag value)
  (if err-flag
      (format nil "~%ERROR: Evaluation failed~%~
                   The expression could not be evaluated successfully.~%~
                   This may be due to:~%~
                   - Guard violation (type mismatch)~%~
                   - Undefined function~%~
                   - Runtime error~%~
                   - Non-terminating computation")
    (format nil "~%RESULT:~%~A" (format-value-for-llm value))))

;;;============================================================================
;;; Main Execution Function
;;;============================================================================

;; Execute ACL2 code from string with full safety
;; Returns a formatted string suitable for LLM consumption
(defun execute-acl2-code (code-str)
  "Safely execute ACL2 code from a string.
   Returns a formatted string with either the result or an error message."
  (handler-case
    (let ((*read-eval* nil))  ; CRITICAL: Prevent #. reader macro attacks
      ;; Step 1: Parse the code string
      (let ((form (read-from-string code-str)))
        ;; Step 2: Security validation
        (unless (code-safe-p-raw form)
          (return-from execute-acl2-code
            (format nil "~%SECURITY ERROR: Code contains forbidden operations.~%~
                        The following are not allowed:~%~
                        - System calls (sys-call)~%~
                        - Trust tags (defttag)~%~
                        - Raw mode (progn!, set-raw-mode)~%~
                        - File I/O (open-input-channel, etc.)~%~
                        - Loading code (include-book, ld)")))
        ;; Step 3: Execute via acl2s-compute
        (let ((result (acl2s-interface-internal::acl2s-compute form :quiet t)))
          (if (and (listp result) (= (length result) 2))
              (let ((err-flag (first result))
                    (value (second result)))
                (format-exec-result err-flag value))
            ;; Unexpected result format
            (format nil "~%INTERNAL ERROR: Unexpected result format")))))
    ;; Error handlers
    (end-of-file (e)
      (declare (ignore e))
      (format nil "~%PARSE ERROR: Incomplete expression - missing closing parenthesis?"))
    (reader-error (e)
      (format nil "~%PARSE ERROR: Invalid syntax - ~A" e))
    (error (e)
      (format nil "~%ERROR: ~A" e))))

;; Execute ACL2 query (for forms that return error triples)
;; Use this for defthm, thm, test?, etc.
(defun execute-acl2-query (code-str)
  "Execute ACL2 query that returns an error triple (thm, defthm, test?, etc.)
   Returns a formatted string with the result."
  (handler-case
    (let ((*read-eval* nil))
      (let ((form (read-from-string code-str)))
        (unless (code-safe-p-raw form)
          (return-from execute-acl2-query
            "SECURITY ERROR: Code contains forbidden operations"))
        (let ((result (acl2s-interface-internal::acl2s-query form :quiet t)))
          (if (and (listp result) (= (length result) 2))
              (let ((err-flag (first result))
                    (value (second result)))
                (if err-flag
                    (format nil "~%QUERY FAILED: The query did not succeed.~%~
                                For theorems, this means the proof failed.~%~
                                For tests, this means a counterexample was found.")
                  (format nil "~%QUERY SUCCEEDED~%Result: ~A" 
                          (format-value-for-llm value))))
            "INTERNAL ERROR: Unexpected result format"))))
    (error (e)
      (format nil "~%ERROR: ~A" e))))

;; Execute ACL2 event (defun, defthm - modifies world)
;; Use with caution as this permanently adds definitions
(defun execute-acl2-event (code-str)
  "Execute ACL2 event that modifies the world (defun, defthm, etc.)
   Returns success/failure. Note: This permanently affects the ACL2 state."
  (handler-case
    (let ((*read-eval* nil))
      (let ((form (read-from-string code-str)))
        (unless (code-safe-p-raw form)
          (return-from execute-acl2-event
            "SECURITY ERROR: Code contains forbidden operations"))
        (let ((result (acl2s-interface-internal::acl2s-event form :quiet t)))
          (if (and (listp result) (= (length result) 2))
              (let ((err-flag (first result)))
                (if err-flag
                    "EVENT FAILED: The event was not admitted."
                  "EVENT SUCCEEDED: Definition/theorem added to world."))
            "INTERNAL ERROR: Unexpected result format"))))
    (error (e)
      (format nil "~%ERROR: ~A" e))))

;;;============================================================================
;;; Convenience Wrappers for Agent
;;;============================================================================

;; High-level function for agent tool call
;; Automatically determines whether to use compute, query, or event
(defun agent-execute-code (code-str &key (mode :compute))
  "Execute code with specified mode:
   :compute - for expressions that return values (default)
   :query   - for queries returning error triples (thm, test?)
   :event   - for events that modify world (defun, defthm)"
  (case mode
    (:compute (execute-acl2-code code-str))
    (:query (execute-acl2-query code-str))
    (:event (execute-acl2-event code-str))
    (otherwise (format nil "ERROR: Invalid mode ~A. Use :compute, :query, or :event" mode))))

;; Print functions for interactive use
(defun print-code-result (code-str)
  "Execute code and print result - for interactive use"
  (format t "~A~%" (execute-acl2-code code-str)))

