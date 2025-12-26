;;;; lisp-to-ipynb.lisp - Convert Lisp source files to Jupyter notebooks
;;;;
;;;; Uses the CL reader to properly parse source files, putting:
;;;; - Standalone comment blocks into markdown cells
;;;; - Code (with contiguous/internal comments) into code cells
;;;;
;;;; Usage: sbcl --script lisp-to-ipynb.lisp [--acl2] input.lisp [output.ipynb]
;;;;
;;;; Cell boundary rules:
;;;; - Blank lines separate cells (groups of content)
;;;; - A group that contains ONLY comments becomes a markdown cell
;;;; - A group that contains ANY code becomes a code cell (comments included)

(defpackage :lisp-to-ipynb
  (:use :cl)
  (:export :main :convert-file))

(in-package :lisp-to-ipynb)

;;; JSON output utilities

(defun json-escape-string (str)
  "Escape a string for JSON output."
  (with-output-to-string (out)
    (loop for char across str do
      (case char
        (#\\ (write-string "\\\\" out))
        (#\" (write-string "\\\"" out))
        (#\Newline (write-string "\\n" out))
        (#\Return (write-string "\\r" out))
        (#\Tab (write-string "\\t" out))
        (t (if (< (char-code char) 32)
               (format out "\\u~4,'0X" (char-code char))
               (write-char char out)))))))

(defun write-json-string (str stream)
  "Write a JSON-escaped string with quotes."
  (write-char #\" stream)
  (write-string (json-escape-string str) stream)
  (write-char #\" stream))

(defun write-json-string-list (strings stream &key (indent 0))
  "Write a list of strings as a JSON array, one string per line."
  (let ((indent-str (make-string indent :initial-element #\Space)))
    (write-char #\[ stream)
    (if (null strings)
        (write-char #\] stream)
        (progn
          (terpri stream)
          (loop for (str . rest) on strings do
            (write-string indent-str stream)
            (write-string "    " stream)
            (write-json-string str stream)
            (when rest (write-char #\, stream))
            (terpri stream))
          (write-string indent-str stream)
          (write-char #\] stream)))))

;;; Source file parsing - reader-based approach

(defstruct source-element
  "An element from the source file."
  (type nil :type (member :comment :code))
  (text "" :type string)
  (start-line 0 :type integer)
  (end-line 0 :type integer))

(defun read-file-content (pathname)
  "Read entire file as a string."
  (with-open-file (stream pathname :direction :input
                          :external-format :utf-8)
    (let* ((len (file-length stream))
           (content (make-string len)))
      (read-sequence content stream)
      ;; Handle potential shorter read due to encoding
      (string-right-trim '(#\Null) content))))

(defun count-newlines-in-range (content start end)
  "Count newlines in content from start to end."
  (count #\Newline content :start start :end (min end (length content))))

(defun skip-whitespace (content pos)
  "Skip whitespace characters, return new position."
  (let ((len (length content)))
    (loop while (and (< pos len)
                     (member (char content pos) '(#\Space #\Tab #\Newline #\Return)))
          do (incf pos))
    pos))

(defun at-comment-p (content pos)
  "Check if position is at start of a comment."
  (and (< pos (length content))
       (char= (char content pos) #\;)))

(defun scan-comment-block (content pos)
  "Scan a block of contiguous comment lines starting at pos.
   Returns (end-pos . text) where text includes all comment lines."
  (let ((len (length content))
        (start pos)
        (end pos))
    ;; Scan all contiguous comment lines
    (loop while (< end len) do
      ;; Skip to start of content on this line (spaces/tabs only)
      (let ((line-content-start end))
        (loop while (and (< line-content-start len)
                         (member (char content line-content-start) '(#\Space #\Tab)))
              do (incf line-content-start))
        ;; Check if this line starts with a comment
        (if (and (< line-content-start len)
                 (char= (char content line-content-start) #\;))
            ;; It's a comment line, scan to end of line
            (progn
              (setf end line-content-start)
              (loop while (and (< end len)
                               (char/= (char content end) #\Newline))
                    do (incf end))
              ;; Include the newline if present
              (when (and (< end len) (char= (char content end) #\Newline))
                (incf end)))
            ;; Not a comment line, we're done
            (return))))
    (cons end (subseq content start end))))

(defun scan-to-next-content (content pos)
  "Skip blank lines only (not comment lines). Returns new position."
  (let ((len (length content)))
    (loop while (< pos len) do
      (let ((line-start pos))
        ;; Check what's on this line
        (loop while (and (< pos len)
                         (member (char content pos) '(#\Space #\Tab)))
              do (incf pos))
        (cond
          ;; End of file
          ((>= pos len) (return pos))
          ;; Newline = blank line, continue
          ((char= (char content pos) #\Newline)
           (incf pos))
          ;; Content found (comment or code)
          (t (return line-start)))))
    pos))

(defun read-form-from-string (content start)
  "Read a Lisp form from content starting at position start.
   Returns (form . end-position) or nil if no form."
  (let ((*read-eval* nil)
        (*package* (find-package :cl-user)))
    (handler-case
        (multiple-value-bind (form end-pos)
            (read-from-string content t nil :start start)
          (declare (ignore form))
          end-pos)
      (error () nil))))

(defun find-form-end (content start)
  "Find where a form ends by using the reader.
   Returns end position in content."
  (read-form-from-string content start))

(defun has-blank-line-before (content pos)
  "Check if there's a blank line between last newline and pos.
   Returns t if there's at least one blank line."
  (let ((len (length content)))
    ;; Skip any leading whitespace on current line
    (let ((check-pos pos))
      (loop while (and (< check-pos len)
                       (member (char content check-pos) '(#\Space #\Tab)))
            do (incf check-pos))
      ;; Check if we're at newline (meaning blank line) or EOF
      (or (>= check-pos len)
          (char= (char content check-pos) #\Newline)))))

(defun scan-code-block (content pos)
  "Scan a code block (possibly with leading comments) starting at pos.
   A code block ends at a blank line (even within multiline strings are kept intact).
   Returns (end-pos . text)."
  (let ((len (length content))
        (start pos)
        (end pos))
    ;; Scan until we hit a blank line
    (loop while (< end len) do
      (let ((line-start end))
        ;; Skip leading whitespace on line
        (loop while (and (< end len)
                         (member (char content end) '(#\Space #\Tab)))
              do (incf end))
        (cond
          ;; End of file
          ((>= end len)
           (return))
          ;; Blank line - end of block
          ((char= (char content end) #\Newline)
           ;; Rewind to line-start (don't include trailing blank lines)
           (setf end line-start)
           (return))
          ;; Comment line - include it, then check for blank line
          ((char= (char content end) #\;)
           (loop while (and (< end len)
                            (char/= (char content end) #\Newline))
                 do (incf end))
           (when (and (< end len) (char= (char content end) #\Newline))
             (incf end)))
          ;; Code form - use the reader
          (t
           (let ((form-end (find-form-end content end)))
             (if form-end
                 (progn
                   (setf end form-end)
                   ;; Now skip trailing whitespace/newlines to find next line
                   (loop while (and (< end len)
                                    (member (char content end) '(#\Space #\Tab)))
                         do (incf end))
                   ;; Include the newline
                   (when (and (< end len) (char= (char content end) #\Newline))
                     (incf end))
                   ;; Check if next line is blank
                   (when (has-blank-line-before content end)
                     (return)))
                 ;; Reader failed, skip to end of line
                 (progn
                   (loop while (and (< end len)
                                    (char/= (char content end) #\Newline))
                         do (incf end))
                   (when (and (< end len) (char= (char content end) #\Newline))
                     (incf end))
                   (return))))))))
    ;; Trim trailing whitespace from the extracted text
    (let ((text (string-right-trim '(#\Space #\Tab #\Newline #\Return)
                                   (subseq content start end))))
      (cons end text))))

(defun parse-source-file (pathname)
  "Parse a Lisp source file into a list of source-elements.
   Uses the CL reader to properly handle forms with multiline strings."
  (let* ((content (read-file-content pathname))
         (len (length content))
         (pos 0)
         (current-line 1)
         (elements '()))
    (loop while (< pos len) do
      ;; Skip blank lines
      (let ((new-pos (scan-to-next-content content pos)))
        (incf current-line (count-newlines-in-range content pos new-pos))
        (setf pos new-pos))
      
      (when (< pos len)
        (let ((start-line current-line))
          (cond
            ;; Comment block - only if it's purely comments until a blank line
            ((at-comment-p content pos)
             ;; Peek ahead to see if there's code before the next blank line
             (let ((peek-pos pos)
                   (found-code nil))
               (loop while (< peek-pos len) do
                 ;; Skip whitespace on line
                 (loop while (and (< peek-pos len)
                                  (member (char content peek-pos) '(#\Space #\Tab)))
                       do (incf peek-pos))
                 (cond
                   ((>= peek-pos len) (return))
                   ((char= (char content peek-pos) #\Newline)
                    ;; Blank line - end of paragraph
                    (return))
                   ((char= (char content peek-pos) #\;)
                    ;; Comment, skip to end of line
                    (loop while (and (< peek-pos len)
                                     (char/= (char content peek-pos) #\Newline))
                          do (incf peek-pos))
                    (when (< peek-pos len) (incf peek-pos)))
                   (t
                    ;; Found code
                    (setf found-code t)
                    (return))))
               
               (if found-code
                   ;; Treat as code block (comments + code together)
                   (let ((result (scan-code-block content pos)))
                     (incf current-line (count-newlines-in-range content pos (car result)))
                     (setf pos (car result))
                     (push (make-source-element
                            :type :code
                            :text (cdr result)
                            :start-line start-line
                            :end-line current-line)
                           elements))
                   ;; Pure comment block
                   (let ((result (scan-comment-block content pos)))
                     (incf current-line (count-newlines-in-range content pos (car result)))
                     (setf pos (car result))
                     (push (make-source-element
                            :type :comment
                            :text (cdr result)
                            :start-line start-line
                            :end-line current-line)
                           elements)))))
            
            ;; Code block
            (t
             (let ((result (scan-code-block content pos)))
               (incf current-line (count-newlines-in-range content pos (car result)))
               (setf pos (car result))
               (push (make-source-element
                      :type :code
                      :text (cdr result)
                      :start-line start-line
                      :end-line current-line)
                     elements)))))))
    (nreverse elements)))

;;; Notebook generation

(defun make-notebook-cell (source-elem kernel-type)
  "Create a notebook cell from a source element.
   kernel-type is :sbcl or :acl2"
  (let* ((is-comment (eq (source-element-type source-elem) :comment))
         (cell-type (if is-comment "raw" "code"))
         (text (source-element-text source-elem))
         (language (if (eq kernel-type :acl2) "acl2" "common-lisp")))
    (list :cell-type cell-type
          :language language
          :text text)))

(defun split-text-to-lines (text)
  "Split text into lines, preserving the notebook source format."
  (let ((lines '())
        (current-line (make-string-output-stream)))
    (loop for char across text do
      (write-char char current-line)
      (when (char= char #\Newline)
        (push (get-output-stream-string current-line) lines)
        (setf current-line (make-string-output-stream))))
    ;; Don't forget the last line (without newline)
    (let ((last (get-output-stream-string current-line)))
      (when (plusp (length last))
        (push last lines)))
    (nreverse lines)))

(defun write-notebook-cell (cell stream first-p)
  "Write a notebook cell to the JSON stream."
  (let* ((cell-type (getf cell :cell-type))
         (language (getf cell :language))
         (text (getf cell :text))
         (lines (split-text-to-lines text))
         (is-code (string= cell-type "code")))
    (unless first-p
      (write-string "," stream)
      (terpri stream))
    (write-string "  {" stream)
    (terpri stream)
    
    ;; cell_type
    (format stream "   \"cell_type\": ~S," cell-type)
    (terpri stream)
    
    (if is-code
        (progn
          ;; execution_count
          (write-string "   \"execution_count\": null," stream)
          (terpri stream)
          ;; metadata with vscode language
          (write-string "   \"metadata\": {" stream)
          (terpri stream)
          (write-string "    \"vscode\": {" stream)
          (terpri stream)
          (format stream "     \"languageId\": ~S" language)
          (terpri stream)
          (write-string "    }" stream)
          (terpri stream)
          (write-string "   }," stream)
          (terpri stream)
          ;; outputs
          (write-string "   \"outputs\": []," stream)
          (terpri stream))
        (progn
          ;; metadata (empty for markdown)
          (write-string "   \"metadata\": {}," stream)
          (terpri stream)))
    
    ;; source
    (write-string "   \"source\": " stream)
    (write-json-string-list lines stream :indent 3)
    (terpri stream)
    
    (write-string "  }" stream)))

(defun write-notebook (cells kernel-type output-stream)
  "Write a complete Jupyter notebook."
  (let ((kernel-name (if (eq kernel-type :acl2) "acl2" "common-lisp"))
        (kernel-display (if (eq kernel-type :acl2) "ACL2" "Common Lisp"))
        (language-name (if (eq kernel-type :acl2) "acl2" "common-lisp")))
    
    (write-string "{" output-stream)
    (terpri output-stream)
    
    ;; cells array
    (write-string " \"cells\": [" output-stream)
    (terpri output-stream)
    
    (loop for cell in cells
          for first = t then nil
          do (write-notebook-cell cell output-stream first))
    
    (terpri output-stream)
    (write-string " ]," output-stream)
    (terpri output-stream)
    
    ;; metadata
    (write-string " \"metadata\": {" output-stream)
    (terpri output-stream)
    (write-string "  \"kernelspec\": {" output-stream)
    (terpri output-stream)
    (format output-stream "   \"display_name\": ~S,~%" kernel-display)
    (format output-stream "   \"language\": ~S,~%" language-name)
    (format output-stream "   \"name\": ~S~%" kernel-name)
    (write-string "  }," output-stream)
    (terpri output-stream)
    (write-string "  \"language_info\": {" output-stream)
    (terpri output-stream)
    (format output-stream "   \"name\": ~S,~%" language-name)
    (write-string "   \"version\": \"\"" output-stream)
    (terpri output-stream)
    (write-string "  }" output-stream)
    (terpri output-stream)
    (write-string " }," output-stream)
    (terpri output-stream)
    
    ;; nbformat
    (write-string " \"nbformat\": 4," output-stream)
    (terpri output-stream)
    (write-string " \"nbformat_minor\": 2" output-stream)
    (terpri output-stream)
    
    (write-string "}" output-stream)
    (terpri output-stream)))

;;; Main entry point

(defun convert-file (input-path output-path kernel-type)
  "Convert a Lisp file to a Jupyter notebook."
  (let* ((elements (parse-source-file input-path))
         (cells (mapcar (lambda (e) (make-notebook-cell e kernel-type)) elements)))
    (with-open-file (out output-path 
                         :direction :output 
                         :if-exists :supersede
                         :if-does-not-exist :create)
      (write-notebook cells kernel-type out))
    (format t "Converted ~A -> ~A~%" input-path output-path)
    (format t "  Created ~D cells~%" (length cells))))

(defun print-usage ()
  (format t "Usage: sbcl --script lisp-to-ipynb.lisp [--acl2] input.lisp [output.ipynb]~%")
  (format t "~%")
  (format t "Options:~%")
  (format t "  --acl2    Set kernel type to ACL2 (default is Common Lisp/SBCL)~%")
  (format t "~%")
  (format t "If output.ipynb is not specified, it will be derived from input.lisp~%"))

(defun main (args)
  "Main entry point. Args should be command line arguments."
  (let ((kernel-type :sbcl)
        (input-file nil)
        (output-file nil)
        (remaining-args args))
    
    ;; Parse --acl2 flag
    (when (and remaining-args (string= (first remaining-args) "--acl2"))
      (setf kernel-type :acl2)
      (pop remaining-args))
    
    ;; Get input file
    (unless remaining-args
      (print-usage)
      (return-from main 1))
    
    (setf input-file (first remaining-args))
    (pop remaining-args)
    
    ;; Get optional output file
    (setf output-file 
          (if remaining-args
              (first remaining-args)
              (concatenate 'string 
                           (subseq input-file 0 
                                   (or (position #\. input-file :from-end t)
                                       (length input-file)))
                           ".ipynb")))
    
    ;; Check input file exists
    (unless (probe-file input-file)
      (format *error-output* "Error: Input file not found: ~A~%" input-file)
      (return-from main 1))
    
    ;; Convert
    (handler-case
        (progn
          (convert-file input-file output-file kernel-type)
          0)
      (error (e)
        (format *error-output* "Error: ~A~%" e)
        1))))

;;; Run if loaded as script
(when (and (boundp 'sb-ext:*posix-argv*)
           (member "--script" sb-ext:*posix-argv* :test #'string=))
  (let* ((args sb-ext:*posix-argv*)
         ;; Skip everything up to and including the .lisp file
         (script-pos (position-if (lambda (a) (search ".lisp" a)) args))
         (actual-args (if script-pos (nthcdr (1+ script-pos) args) nil)))
    (sb-ext:exit :code (main actual-args))))
