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

;;; Source file parsing - paren-depth tracking approach
;;; This avoids using READ which would require package definitions

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

(defun skip-line-comment (content pos)
  "Skip from ; to end of line. Returns position after newline (or EOF)."
  (let ((len (length content)))
    (loop while (and (< pos len) (char/= (char content pos) #\Newline))
          do (incf pos))
    (when (and (< pos len) (char= (char content pos) #\Newline))
      (incf pos))
    pos))

(defun skip-block-comment (content pos)
  "Skip #|...|# block comment. pos should be at the #. Returns position after |#."
  (let ((len (length content))
        (depth 1))
    ;; Skip the opening #|
    (incf pos 2)
    (loop while (and (< pos (1- len)) (> depth 0)) do
      (cond
        ((and (char= (char content pos) #\|)
              (char= (char content (1+ pos)) #\#))
         (decf depth)
         (incf pos 2))
        ((and (char= (char content pos) #\#)
              (char= (char content (1+ pos)) #\|))
         (incf depth)
         (incf pos 2))
        (t (incf pos))))
    pos))

(defun skip-string (content pos)
  "Skip a string literal starting at pos (which should be at opening \").
   Returns position after closing \"."
  (let ((len (length content)))
    (incf pos) ; skip opening "
    (loop while (< pos len) do
      (let ((ch (char content pos)))
        (cond
          ((char= ch #\\)
           ;; Escape sequence, skip next char
           (incf pos 2))
          ((char= ch #\")
           ;; End of string
           (incf pos)
           (return))
          (t (incf pos)))))
    pos))

(defun skip-character-literal (content pos)
  "Skip #\\... character literal. pos should be at #. Returns position after literal."
  (let ((len (length content)))
    (incf pos 2) ; skip #\
    ;; Handle named characters like #\Newline, #\Space
    (when (< pos len)
      (if (alpha-char-p (char content pos))
          ;; Named character - read until non-alphanumeric
          (loop while (and (< pos len)
                           (alphanumericp (char content pos)))
                do (incf pos))
          ;; Single character already consumed
          ))
    pos))

(defun find-form-end-by-depth (content start)
  "Find the end of a Lisp form by tracking paren depth.
   Handles strings, comments, character literals correctly.
   Returns end position or nil if no valid form."
  (let ((len (length content))
        (pos start)
        (depth 0)
        (started nil))
    ;; Skip leading whitespace
    (loop while (and (< pos len)
                     (member (char content pos) '(#\Space #\Tab #\Newline #\Return)))
          do (incf pos))
    (when (>= pos len)
      (return-from find-form-end-by-depth nil))
    
    ;; Determine what kind of form we have
    (let ((ch (char content pos)))
      (cond
        ;; S-expression starting with (
        ((char= ch #\()
         (setf started t)
         (incf depth)
         (incf pos))
        ;; Quote, backquote, comma - followed by another form
        ((member ch '(#\' #\` #\,))
         (incf pos)
         ;; Handle ,@ 
         (when (and (< pos len) (char= ch #\,) (char= (char content pos) #\@))
           (incf pos))
         ;; Recursively find the quoted form
         (return-from find-form-end-by-depth
           (find-form-end-by-depth content pos)))
        ;; Hash reader macros
        ((char= ch #\#)
         (when (< (1+ pos) len)
           (let ((next (char content (1+ pos))))
             (cond
               ;; #| block comment - but this shouldn't start a form
               ((char= next #\|)
                (return-from find-form-end-by-depth nil))
               ;; #\ character literal
               ((char= next #\\)
                (return-from find-form-end-by-depth
                  (skip-character-literal content pos)))
               ;; #' function quote
               ((char= next #\')
                (incf pos 2)
                (return-from find-form-end-by-depth
                  (find-form-end-by-depth content pos)))
               ;; #( vector
               ((char= next #\()
                (setf started t)
                (incf depth)
                (incf pos 2))
               ;; Other # forms - treat as atom until whitespace/paren
               (t
                (incf pos)
                (loop while (and (< pos len)
                                 (not (member (char content pos)
                                              '(#\Space #\Tab #\Newline #\Return
                                                #\( #\) #\; #\"))))
                      do (incf pos))
                (return-from find-form-end-by-depth pos))))))
        ;; String
        ((char= ch #\")
         (return-from find-form-end-by-depth
           (skip-string content pos)))
        ;; Comment - not a form
        ((char= ch #\;)
         (return-from find-form-end-by-depth nil))
        ;; Atom (symbol, number, keyword)
        (t
         ;; Read until delimiter
         (loop while (and (< pos len)
                          (not (member (char content pos)
                                       '(#\Space #\Tab #\Newline #\Return
                                         #\( #\) #\; #\"))))
               do (incf pos))
         (return-from find-form-end-by-depth pos))))
    
    ;; Now scan through the s-expression tracking depth
    (loop while (and (< pos len) (or (not started) (> depth 0))) do
      (let ((ch (char content pos)))
        (cond
          ;; Opening paren
          ((char= ch #\()
           (setf started t)
           (incf depth)
           (incf pos))
          ;; Closing paren
          ((char= ch #\))
           (decf depth)
           (incf pos))
          ;; String literal
          ((char= ch #\")
           (setf pos (skip-string content pos)))
          ;; Line comment
          ((char= ch #\;)
           (setf pos (skip-line-comment content pos)))
          ;; Hash reader macros
          ((char= ch #\#)
           (if (< (1+ pos) len)
               (let ((next (char content (1+ pos))))
                 (cond
                   ((char= next #\|)
                    (setf pos (skip-block-comment content pos)))
                   ((char= next #\\)
                    (setf pos (skip-character-literal content pos)))
                   ((char= next #\()
                    (incf depth)
                    (incf pos 2))
                   (t (incf pos))))
               (incf pos)))
          ;; Regular character
          (t (incf pos)))))
    
    (if (zerop depth)
        pos
        nil)))

(defun at-comment-p (content pos)
  "Check if position is at start of a comment."
  (and (< pos (length content))
       (char= (char content pos) #\;)))

(defun scan-to-content (content pos)
  "Skip whitespace only (not past content). Returns new position."
  (let ((len (length content)))
    (loop while (and (< pos len)
                     (member (char content pos) '(#\Space #\Tab #\Newline #\Return)))
          do (incf pos))
    pos))

(defun scan-comment-block (content pos)
  "Scan a block of contiguous comment lines starting at pos.
   Returns (end-pos . text)."
  (let ((len (length content))
        (start pos)
        (end pos))
    (loop while (< end len) do
      ;; Skip leading whitespace on this line (but not past newline)
      (let ((line-start end))
        (loop while (and (< end len)
                         (member (char content end) '(#\Space #\Tab)))
              do (incf end))
        (cond
          ;; End of file
          ((>= end len)
           (return))
          ;; Blank line - end of comment block
          ((char= (char content end) #\Newline)
           (setf end line-start)
           (return))
          ;; Another comment line
          ((char= (char content end) #\;)
           (setf end (skip-line-comment content end)))
          ;; Non-comment content - end of block
          (t
           (setf end line-start)
           (return)))))
    (cons end (string-right-trim '(#\Newline #\Return)
                                  (subseq content start end)))))

(defun has-blank-line-after (content pos)
  "Check if there's a blank line starting at pos."
  (let ((len (length content)))
    (loop while (and (< pos len)
                     (member (char content pos) '(#\Space #\Tab)))
          do (incf pos))
    (or (>= pos len)
        (char= (char content pos) #\Newline))))

(defun scan-code-block (content pos)
  "Scan a code block starting at pos, using paren-depth tracking.
   Code blocks end at blank lines.
   Returns (end-pos . text)."
  (let ((len (length content))
        (start pos)
        (end pos))
    (loop while (< end len) do
      (let ((line-start end))
        ;; Skip leading whitespace on this line
        (loop while (and (< end len)
                         (member (char content end) '(#\Space #\Tab)))
              do (incf end))
        (cond
          ;; End of file
          ((>= end len)
           (return))
          ;; Blank line - end of block
          ((char= (char content end) #\Newline)
           (setf end line-start)
           (return))
          ;; Comment line within code block - include it
          ((char= (char content end) #\;)
           (setf end (skip-line-comment content end)))
          ;; Code form
          (t
           (let ((form-end (find-form-end-by-depth content end)))
             (if form-end
                 (progn
                   (setf end form-end)
                   ;; Skip trailing whitespace (but not newlines yet)
                   (loop while (and (< end len)
                                    (member (char content end) '(#\Space #\Tab)))
                         do (incf end))
                   ;; Include the newline if present
                   (when (and (< end len) (char= (char content end) #\Newline))
                     (incf end))
                   ;; Check if next line is blank
                   (when (has-blank-line-after content end)
                     (return)))
                 ;; No valid form found, skip line
                 (progn
                   (loop while (and (< end len)
                                    (char/= (char content end) #\Newline))
                         do (incf end))
                   (when (and (< end len) (char= (char content end) #\Newline))
                     (incf end)))))))))
    (cons end (string-right-trim '(#\Space #\Tab #\Newline #\Return)
                                  (subseq content start end)))))

(defun parse-source-file (pathname)
  "Parse a Lisp source file into a list of source-elements.
   Uses paren-depth tracking to handle forms without needing package defs."
  (let* ((content (read-file-content pathname))
         (len (length content))
         (pos 0)
         (current-line 1)
         (elements '()))
    (loop while (< pos len) do
      ;; Skip blank lines
      (let ((new-pos (scan-to-content content pos)))
        (incf current-line (count-newlines-in-range content pos new-pos))
        (setf pos new-pos))
      
      (when (< pos len)
        (let ((start-line current-line))
          (cond
            ;; Comment block - check if it's pure comments until blank line
            ((at-comment-p content pos)
             ;; Look ahead to see if there's code before blank line
             (let ((peek-pos pos)
                   (found-code nil))
               (loop while (< peek-pos len) do
                 (loop while (and (< peek-pos len)
                                  (member (char content peek-pos) '(#\Space #\Tab)))
                       do (incf peek-pos))
                 (cond
                   ((>= peek-pos len) (return))
                   ((char= (char content peek-pos) #\Newline) (return))
                   ((char= (char content peek-pos) #\;)
                    (setf peek-pos (skip-line-comment content peek-pos)))
                   (t (setf found-code t) (return))))
               
               (if found-code
                   ;; Comments + code = code block
                   (let ((result (scan-code-block content pos)))
                     (incf current-line (count-newlines-in-range content pos (car result)))
                     (setf pos (car result))
                     (push (make-source-element
                            :type :code
                            :text (cdr result)
                            :start-line start-line
                            :end-line current-line)
                           elements))
                   ;; Pure comments
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
;;; With sbcl --script foo.lisp arg1 arg2, *posix-argv* is ("foo.lisp" "arg1" "arg2")
(when (boundp 'sb-ext:*posix-argv*)
  (let ((args (cdr sb-ext:*posix-argv*))) ; skip script name
    (when args
      (sb-ext:exit :code (main args)))))
