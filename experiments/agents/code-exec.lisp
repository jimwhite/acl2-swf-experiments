; code-exec.lisp - Safe ACL2 Code Execution for Verified Agent
;
; Provides sandboxed ACL2 code execution using acl2s-compute, similar to 
; how mini-swe-agent uses bash, but for theorem proving and computation.
;
; Key safety features:
; - Uses acl2s-compute which catches hard errors
; - Validated against forbidden functions list
; - Requires execute permission in agent state
; - Returns structured results (success/error + value)
;
; Usage:
;   (include-book "code-exec" :ttags ((:acl2s-interface) (:code-exec)))
;   ;; Then in raw Lisp:
;   (execute-acl2-code "(+ 1 2)")  ; => "RESULT: 3"

(in-package "ACL2")

;;;============================================================================
;;; Part 1: Library Imports
;;;============================================================================

(include-book "tools/include-raw" :dir :system)
(include-book "acl2s/aspf/interface/top" :dir :system 
              :ttags ((:acl2s-interface)))
(include-book "std/strings/top" :dir :system)

;;;============================================================================
;;; Part 2: Forbidden Patterns (Security)
;;;============================================================================

;; List of forbidden function/macro symbols that could break safety
(defconst *forbidden-symbols*
  '(;; System calls and raw Lisp access
    sys-call sys-call-status sys-call+
    set-raw-mode set-raw-mode-on set-raw-mode-on!
    progn! with-raw-mode
    ;; Trust tag manipulation
    defttag 
    ;; Untouchable manipulation
    remove-untouchable push-untouchable
    ;; File system operations (use tools instead)
    open-input-channel open-output-channel
    read-file-into-string
    ;; State mutation that could escape sandbox
    assign f-put-global
    ;; Loading external code
    include-book ld load include-raw
    ;; Package manipulation  
    defpkg in-package))

;; Check if a symbol is forbidden
(defun forbidden-symbol-p (sym)
  (declare (xargs :guard t))
  (and (symbolp sym)
       (member-equal sym *forbidden-symbols*)))

;;;============================================================================
;;; Part 3: Code Validation (Pure ACL2)
;;;============================================================================

;; Check if form contains any forbidden symbols (recursive)
;; Returns t if form is SAFE, nil if it contains forbidden content
(defun code-safe-p (form)
  (declare (xargs :guard t))
  (cond
   ;; Base case: atom
   ((atom form)
    (not (forbidden-symbol-p form)))
   ;; Recursive case: cons
   (t (and (code-safe-p (car form))
           (code-safe-p (cdr form))))))

;; Validate code string before evaluation
;; Returns (mv safe-p reason)
(defun validate-code-string (code-str)
  (declare (xargs :guard (stringp code-str) :mode :program))
  ;; Simple pattern checks before parsing
  (cond
   ;; Check for common dangerous patterns in string form
   ((search "defttag" code-str)
    (mv nil "Code contains defttag - trust tags not allowed"))
   ((search "sys-call" code-str)
    (mv nil "Code contains sys-call - system calls not allowed"))
   ((search "set-raw-mode" code-str)
    (mv nil "Code contains set-raw-mode - raw mode not allowed"))
   ((search "progn!" code-str)
    (mv nil "Code contains progn! - raw Lisp forms not allowed"))
   ((search "include-book" code-str)
    (mv nil "Code contains include-book - use tools instead"))
   ((search "include-raw" code-str)
    (mv nil "Code contains include-raw - raw files not allowed"))
   (t (mv t nil))))

;;;============================================================================
;;; Part 4: Result Formatting
;;;============================================================================

;; Format the result of acl2s-compute for LLM consumption
(defun format-compute-result (result)
  (declare (xargs :guard t :mode :program))
  (if (and (consp result) (= (len result) 2))
      (let ((err-flag (first result))
            (value (second result)))
        (if err-flag
            ;; Error case
            (concatenate 'string
                         "ERROR: Evaluation failed\n"
                         "The expression could not be evaluated. "
                         "This may be due to a guard violation, "
                         "undefined function, or runtime error.")
          ;; Success case - format value as string
          (let ((val-str (coerce (packn1 (list value)) 'string)))
            (concatenate 'string "RESULT: " val-str))))
    ;; Unexpected format
    "ERROR: Unexpected result format from evaluator"))

;;;============================================================================
;;; Part 5: Safe Evaluation Interface (Program Mode)
;;;============================================================================

;; Parse a string into an ACL2 form
;; Returns (mv erp form) where erp is error message or nil
(defun parse-code-string (code-str state)
  (declare (xargs :guard (stringp code-str)
                  :mode :program
                  :stobjs state))
  ;; Use read-from-string via trans-eval
  (mv-let (erp val state)
    (read-acl2-oracle state)  ; Dummy read for state threading
    (declare (ignore erp val))
    ;; We'll use acl2s-compute to do the parsing safely
    (mv nil (list 'quote code-str) state)))

;; Execute ACL2 code string safely (Program mode - requires state)
;; Returns (mv error-p result-string state)
;;
;; This is the main entry point for the verified agent's code execution tool.
;; It validates the code, executes it using acl2s-compute, and formats results.
(defun safe-eval (code-str state)
  (declare (xargs :guard (stringp code-str)
                  :mode :program
                  :stobjs state))
  (b* (;; Step 1: Validate code string for forbidden patterns
       ((mv safe-p reason) (validate-code-string code-str))
       ((when (not safe-p))
        (mv t (concatenate 'string "SECURITY ERROR: " reason) state)))
    ;; Step 2: Execute via acl2s-compute 
    ;; Note: We need to drop to raw Lisp to call acl2s-compute
    (mv nil 
        (concatenate 'string 
                     "Code passed validation: " code-str
                     "\nNote: Actual execution requires raw Lisp bridge")
        state)))

;;;============================================================================
;;; Part 6: Tool Specification for Verified Agent
;;;============================================================================

;; Tool spec for code execution (uses verified-agent types when loaded together)
;; Note: This is just the constant data; actual tool-spec requires verified-agent
(defconst *code-exec-tool-spec*
  '(:name execute-acl2-code
    :required-access 0      ; No file access needed
    :requires-execute t     ; REQUIRES execute permission!
    :token-cost 500         ; Generous token budget for results
    :time-cost 30))         ; 30 seconds max

;;;============================================================================
;;; Part 7: Raw Lisp Bridge
;;;============================================================================

;; Load the raw Lisp implementation
;; This provides: execute-acl2-code, execute-acl2-query, execute-acl2-event
(defttag :code-exec)
(include-raw "code-exec-raw.lsp")

;;;============================================================================
;;; Part 8: ACL2 Interface to Raw Functions
;;;============================================================================

;; These functions call the raw Lisp implementations and are usable from ACL2.
;; They require trust tags because they access raw Lisp.

;; Execute ACL2 code and return string result
;; Usage: :q then (execute-acl2-code "(+ 1 2)") in raw Lisp
;; Or use the make-event pattern from ACL2

;; For interactive use from ACL2, we provide a make-event based wrapper
;; that allows calling the raw function and capturing its output

#||
Example usage in ACL2 (after including this book):

;; Method 1: From raw Lisp
:q
(execute-acl2-code "(+ 1 2)")
; => "RESULT: 3"
(lp)

;; Method 2: Using make-event to capture result into a constant
(make-event
 (let ((result (execute-acl2-code "(append '(1 2) '(3 4))")))
   (mv nil `(defconst *last-result* ,result) state)))

;; Method 3: For queries (thm, test?)
:q
(execute-acl2-query "(thm (equal (+ 1 1) 2))")
; => "QUERY SUCCEEDED..."
(lp)
||#
