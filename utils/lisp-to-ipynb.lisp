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

;;; Source file parsing - character-based approach

(defstruct source-element
  "An element from the source file."
  (type nil :type (member :comment :code))
  (text "" :type string)
  (start-line 0 :type integer)
  (end-line 0 :type integer))

(defun read-file-lines (pathname)
  "Read file as a list of lines (without newlines)."
  (with-open-file (stream pathname :direction :input)
    (loop for line = (read-line stream nil nil)
          while line
          collect line)))

(defun blank-line-p (line)
  "Check if a line is blank (empty or only whitespace)."
  (every (lambda (c) (member c '(#\Space #\Tab))) line))

(defun comment-line-p (line)
  "Check if a line is a comment (starts with ; after optional whitespace)."
  (let ((trimmed (string-left-trim '(#\Space #\Tab) line)))
    (and (plusp (length trimmed))
         (char= (char trimmed 0) #\;))))

(defun group-lines-by-blanks (lines)
  "Group consecutive non-blank lines together.
   Returns list of (line-list start-line-num) pairs."
  (let ((groups '())
        (current-group '())
        (current-start 1)
        (line-num 0))
    (dolist (line lines)
      (incf line-num)
      (if (blank-line-p line)
          ;; Blank line: close current group if any
          (when current-group
            (push (list (nreverse current-group) current-start) groups)
            (setf current-group '()))
          ;; Non-blank line: add to current group
          (progn
            (when (null current-group)
              (setf current-start line-num))
            (push line current-group))))
    ;; Don't forget the last group
    (when current-group
      (push (list (nreverse current-group) current-start) groups))
    (nreverse groups)))

(defun all-comments-p (lines)
  "Check if all lines in a list are comments."
  (every #'comment-line-p lines))

(defun classify-group (lines)
  "Classify a group as :comment or :code based on its content."
  (if (all-comments-p lines)
      :comment
      :code))

(defun parse-source-file (pathname)
  "Parse a Lisp source file into a list of source-elements.
   Groups lines by blank line separators, then classifies each group."
  (let* ((lines (read-file-lines pathname))
         (groups (group-lines-by-blanks lines)))
    (mapcar (lambda (group-info)
              (let* ((group-lines (first group-info))
                     (start-line (second group-info))
                     (group-type (classify-group group-lines))
                     (text (format nil "~{~A~^~%~}" group-lines)))
                (make-source-element
                 :type group-type
                 :text text
                 :start-line start-line
                 :end-line (+ start-line (1- (length group-lines))))))
            groups)))

;;; Convert comments to markdown format

(defun strip-comment-prefix (line)
  "Remove leading semicolons and one space from a comment line."
  (let ((start 0)
        (len (length line)))
    ;; Skip leading whitespace
    (loop while (and (< start len) 
                     (member (char line start) '(#\Space #\Tab)))
          do (incf start))
    ;; Skip semicolons
    (loop while (and (< start len) (char= (char line start) #\;))
          do (incf start))
    ;; Skip one space after semicolons if present
    (when (and (< start len) (char= (char line start) #\Space))
      (incf start))
    (subseq line start)))

(defun comment-to-markdown (comment-text)
  "Convert comment text to markdown by stripping ; prefixes."
  (with-output-to-string (out)
    (with-input-from-string (in comment-text)
      (loop for line = (read-line in nil nil)
            for first = t then nil
            while line do
        (unless first (terpri out))
        (write-string (strip-comment-prefix line) out)))))

;;; Notebook generation

(defun make-notebook-cell (source-elem kernel-type)
  "Create a notebook cell from a source element.
   kernel-type is :sbcl or :acl2"
  (let* ((is-comment (eq (source-element-type source-elem) :comment))
         (cell-type (if is-comment "markdown" "code"))
         (text (if is-comment
                   (comment-to-markdown (source-element-text source-elem))
                   (source-element-text source-elem)))
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
