; code-exec.lisp - ACL2 Code Execution via ACL2s Interface
;
; Provides code execution for the verified agent using acl2s-compute from
; the ACL2s interface books. The LLM sends code in markdown blocks,
; we extract and execute it, returning results as strings.
;
; Key features:
; - Uses acl2s-compute directly (no custom wrappers)
; - Extracts code from ```acl2 and ```lisp markdown blocks
; - Returns error messages to help LLM learn
; - Integrates with verified agent's execute-allowed permission
;
; Usage:
;   (include-book "code-exec" :ttags :all)
;   (acl2s-interface::acl2s-compute '(+ 1 2))  ; => (NIL 3)

(in-package "ACL2")

;;;============================================================================
;;; Part 1: Library Imports
;;;============================================================================

;; ACL2s interface provides acl2s-compute, acl2s-query, acl2s-event
(include-book "acl2s/interface/top" :dir :system :ttags :all)

;; String utilities
(include-book "std/strings/top" :dir :system)

;;;============================================================================
;;; Part 2: Constants for Code Block Detection
;;;============================================================================

;; Markdown code fence markers
;; LLMs use either ```acl2 or ```lisp for ACL2 code
(defconst *code-fence-acl2* "```acl2")
(defconst *code-fence-lisp* "```lisp") 
(defconst *code-fence-end* "```")

;; Output limits
(defconst *max-result-chars* 2000)

;;;============================================================================
;;; Part 3: String Search Utilities (Program Mode)
;;;============================================================================

;; Find substring in string, returns position or nil
(defun find-substring (needle haystack start)
  (declare (xargs :guard (and (stringp needle)
                              (stringp haystack)
                              (natp start))
                  :mode :program))
  (let ((needle-len (length needle))
        (haystack-len (length haystack)))
    (cond
     ((> (+ start needle-len) haystack-len) nil)
     ((string-equal needle (subseq haystack start (+ start needle-len))) start)
     (t (find-substring needle haystack (1+ start))))))

;; Find next occurrence after given position
(defun find-next (needle haystack after-pos)
  (declare (xargs :guard (and (stringp needle)
                              (stringp haystack)
                              (natp after-pos))
                  :mode :program))
  (find-substring needle haystack after-pos))

;;;============================================================================
;;; Part 4: Code Block Extraction
;;;============================================================================

;; Extract content between start-pos and end fence
(defun extract-block-content (text start-pos fence-end)
  (declare (xargs :guard (and (stringp text)
                              (natp start-pos)
                              (stringp fence-end))
                  :mode :program))
  (let ((end-pos (find-next fence-end text start-pos)))
    (if end-pos
        (str::trim (subseq text start-pos end-pos))
      nil)))

;; Find the start of code content (after fence line)
(defun find-code-start (text fence-pos fence-len)
  (declare (xargs :guard (and (stringp text)
                              (natp fence-pos)
                              (natp fence-len))
                  :mode :program))
  (let ((newline-pos (find-next (coerce '(#\Newline) 'string) 
                                text 
                                (+ fence-pos fence-len))))
    (if newline-pos
        (1+ newline-pos)
      nil)))

;; Extract first code block from text (either ```acl2 or ```lisp)
(defun extract-first-code-block (text)
  (declare (xargs :guard (stringp text)
                  :mode :program))
  (let* ((acl2-pos (find-next *code-fence-acl2* text 0))
         (lisp-pos (find-next *code-fence-lisp* text 0))
         (fence-pos (cond ((and acl2-pos lisp-pos) (min acl2-pos lisp-pos))
                          (acl2-pos acl2-pos)
                          (lisp-pos lisp-pos)
                          (t nil)))
         (fence-len (cond ((and fence-pos acl2-pos (= fence-pos acl2-pos))
                           (length *code-fence-acl2*))
                          ((and fence-pos lisp-pos (= fence-pos lisp-pos))
                           (length *code-fence-lisp*))
                          (t 0))))
    (if fence-pos
        (let ((code-start (find-code-start text fence-pos fence-len)))
          (if code-start
              (extract-block-content text code-start *code-fence-end*)
            nil))
      nil)))

;; Extract all code blocks from text
(defun extract-all-code-blocks-aux (text start acc)
  (declare (xargs :guard (and (stringp text)
                              (natp start)
                              (true-listp acc))
                  :mode :program))
  (if (>= start (length text))
      (reverse acc)
    (let* ((acl2-pos (find-next *code-fence-acl2* text start))
           (lisp-pos (find-next *code-fence-lisp* text start))
           (fence-pos (cond ((and acl2-pos lisp-pos) (min acl2-pos lisp-pos))
                            (acl2-pos acl2-pos)
                            (lisp-pos lisp-pos)
                            (t nil))))
      (if (null fence-pos)
          (reverse acc)
        (let* ((fence-len (if (and acl2-pos (= fence-pos acl2-pos))
                              (length *code-fence-acl2*)
                            (length *code-fence-lisp*)))
               (code-start (find-code-start text fence-pos fence-len)))
          (if (null code-start)
              (reverse acc)
            (let* ((end-pos (find-next *code-fence-end* text code-start))
                   (code (if end-pos
                            (str::trim (subseq text code-start end-pos))
                          nil)))
              (if (and code (> (length code) 0))
                  (extract-all-code-blocks-aux 
                   text 
                   (if end-pos (+ end-pos (length *code-fence-end*)) (length text))
                   (cons code acc))
                (reverse acc)))))))))

(defun extract-all-code-blocks (text)
  (declare (xargs :guard (stringp text)
                  :mode :program))
  (extract-all-code-blocks-aux text 0 nil))

;;;============================================================================
;;; Part 5: Value to String Conversion
;;;============================================================================

;; Convert atom to string
(defun atom-to-string (x)
  (declare (xargs :guard (atom x) :mode :program))
  (cond
   ((null x) "NIL")
   ((symbolp x) (symbol-name x))
   ((stringp x) (concatenate 'string "\"" x "\""))
   ((integerp x) (str::natstr (if (< x 0) (- x) x)))
   ((characterp x) (coerce (list #\# #\\ x) 'string))
   (t "<atom>")))

;; Convert S-expression to string (simple, non-pretty)
(defun sexp-to-string (x)
  (declare (xargs :guard t :mode :program))
  (cond
   ((atom x) (atom-to-string x))
   ((null (cdr x)) 
    (concatenate 'string "(" (sexp-to-string (car x)) ")"))
   (t (concatenate 'string 
                   "(" 
                   (sexp-to-string (car x))
                   " "
                   (sexp-list-to-string (cdr x))
                   ")"))))

(defun sexp-list-to-string (lst)
  (declare (xargs :guard t :mode :program))
  (cond
   ((atom lst) 
    (if (null lst) "" (concatenate 'string ". " (atom-to-string lst))))
   ((null (cdr lst))
    (sexp-to-string (car lst)))
   (t (concatenate 'string 
                   (sexp-to-string (car lst))
                   " "
                   (sexp-list-to-string (cdr lst))))))

;;;============================================================================
;;; Part 6: Result Formatting
;;;============================================================================

;; Truncate string if too long
(defun truncate-result (str max-len)
  (declare (xargs :guard (and (stringp str) (natp max-len))
                  :mode :program))
  (if (<= (length str) max-len)
      str
    (concatenate 'string 
                 (subseq str 0 (max 0 (- max-len 20)))
                 "... [truncated]")))

;; Format a successful result
(defun format-success (value)
  (declare (xargs :guard t :mode :program))
  (let* ((val-str (sexp-to-string value))
         (truncated (truncate-result val-str *max-result-chars*)))
    (concatenate 'string "Result: " truncated)))

;; Format an error result
(defun format-error (captured-output)
  (declare (xargs :guard (stringp captured-output) :mode :program))
  (concatenate 'string 
               "Error: Evaluation failed\n"
               (truncate-result captured-output *max-result-chars*)))

;; Format acl2s-compute result: (error-flag value)
(defun format-compute-result (result captured-output)
  (declare (xargs :guard t :mode :program))
  (if (and (consp result) (= (len result) 2))
      (let ((err-flag (first result))
            (value (second result)))
        (if err-flag
            (format-error (if (and (stringp captured-output)
                                   (> (length captured-output) 0))
                              captured-output
                            "Unknown error"))
          (format-success value)))
    "Error: Unexpected result format"))

;;;============================================================================
;;; Part 7: Code Execution via acl2s-compute
;;;============================================================================

;; Execute a code string via acl2s-compute
;; Returns formatted result string
(defun execute-code (code-str)
  (declare (xargs :guard (stringp code-str) :mode :program))
  ;; Parse the code string to S-expression
  (mv-let (erp form state)
    (acl2::read-object (coerce code-str 'list) state)
    (declare (ignore state))
    (if erp
        (concatenate 'string "Error: Parse error in code")
      ;; Execute via acl2s-compute
      (let ((result (acl2s-interface::acl2s-compute form :quiet t)))
        (format-compute-result result "")))))

;; Execute all code blocks from LLM response
(defun execute-code-blocks-aux (blocks acc)
  (declare (xargs :guard (and (true-listp blocks) (true-listp acc))
                  :mode :program))
  (if (endp blocks)
      (reverse acc)
    (let* ((code (car blocks))
           (result (execute-code code)))
      (execute-code-blocks-aux (cdr blocks) (cons (cons code result) acc)))))

(defun execute-code-blocks (text)
  (declare (xargs :guard (stringp text) :mode :program))
  (let ((blocks (extract-all-code-blocks text)))
    (execute-code-blocks-aux blocks nil)))

;;;============================================================================
;;; Part 8: Tool Specification for Verified Agent
;;;============================================================================

;; Tool spec constant (compatible with verified-agent.lisp tool-spec structure)
(defconst *code-exec-tool-spec*
  '(acl2-compute    ; name
    0               ; required-access (none)
    t               ; requires-execute
    200             ; token-cost
    10))            ; time-cost
