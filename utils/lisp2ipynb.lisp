#!/usr/bin/env sbcl --script
;;;; lisp2ipynb.lisp
;;;;
;;;; Convert SBCL/ACL2 Lisp source files to Jupyter notebooks (.ipynb)
;;;; Uses SBCL reader syntactically (no interning, no package resolution)
;;;;
;;;; Usage: sbcl --script lisp2ipynb.lisp input.lisp output.ipynb
;;;;    or: ./lisp2ipynb.lisp input.lisp output.ipynb

(defpackage :lisp2ipynb
  (:use :cl)
  (:export #:convert-file))

(in-package :lisp2ipynb)

;;;; JSON Output Utilities

(defun json-escape-string (str)
  "Escape string for JSON output."
  (with-output-to-string (out)
    (loop for ch across str do
      (case ch
        (#\" (write-string "\\\"" out))
        (#\\ (write-string "\\\\" out))
        (#\Newline (write-string "\\n" out))
        (#\Return (write-string "\\r" out))
        (#\Tab (write-string "\\t" out))
        (t (write-char ch out))))))

(defun write-json-string (str stream)
  "Write a JSON string to stream."
  (write-char #\" stream)
  (write-string (json-escape-string str) stream)
  (write-char #\" stream))

(defun write-json-array (items stream &key newlines indent)
  "Write JSON array to stream."
  (write-char #\[ stream)
  (loop for item in items
        for first = t then nil
        do (progn
             (unless first (write-char #\, stream))
             (when newlines 
               (terpri stream)
               (dotimes (i indent) (write-char #\Space stream)))
             (cond
               ((stringp item) (write-json-string item stream))
               ((null item) (write-string "null" stream))
               ((numberp item) (format stream "~A" item))
               ((eq item :null) (write-string "null" stream))
               (t (funcall item stream)))))
  (write-char #\] stream))

(defun write-json-object (alist stream &key newlines indent)
  "Write JSON object from alist to stream."
  (write-char #\{ stream)
  (loop for (key . value) in alist
        for first = t then nil
        do (progn
             (unless first (write-char #\, stream))
             (when newlines 
               (terpri stream)
               (dotimes (i indent) (write-char #\Space stream)))
             (write-json-string (string key) stream)
             (write-char #\: stream)
             (cond
               ((stringp value) (write-json-string value stream))
               ((null value) (write-string "null" stream))
               ((numberp value) (format stream "~A" value))
               ((eq value :null) (write-string "null" stream))
               ((eq value t) (write-string "true" stream))
               ((listp value) 
                (if (listp (car value))
                    (write-json-object value stream :indent (+ indent 2))
                    (write-json-array value stream)))
               (t (funcall value stream)))))
  (write-char #\} stream))

;;;; Syntactic Reader (No Interning)

(defun skip-whitespace (stream)
  "Skip whitespace characters."
  (loop for ch = (peek-char nil stream nil)
        while (and ch (member ch '(#\Space #\Tab #\Newline #\Return #\Page)))
        do (read-char stream)))

(defun read-line-comment (stream)
  "Read a line comment (starting with ;)."
  (read-char stream) ; consume ;
  (with-output-to-string (out)
    (loop for ch = (read-char stream nil nil)
          while (and ch (not (eq ch #\Newline)))
          do (write-char ch out))))

(defun read-block-comment (stream)
  "Read a block comment #| ... |# with nesting."
  (read-char stream) ; consume #
  (read-char stream) ; consume |
  (with-output-to-string (out)
    (let ((depth 1))
      (loop while (> depth 0)
            for ch = (read-char stream nil nil)
            while ch
            do (progn
                 ;; Check for #|
                 (when (and (eq ch #\#) 
                           (eq (peek-char nil stream nil) #\|))
                   (read-char stream)
                   (incf depth)
                   (write-char ch out)
                   (write-char #\| out)
                   (go continue))
                 ;; Check for |#
                 (when (and (eq ch #\|) 
                           (eq (peek-char nil stream nil) #\#))
                   (read-char stream)
                   (decf depth)
                   (unless (zerop depth)
                     (write-char ch out)
                     (write-char #\# out))
                   (go continue))
                 ;; Regular character
                 (write-char ch out)
                 continue)))))

(defun read-form-source (stream)
  "Read a complete form as source text without interning."
  (with-output-to-string (out)
    (let ((depth 0)
          (in-string nil)
          (escape-next nil))
      
      (loop
        (let ((ch (peek-char nil stream nil)))
          (when (null ch) (return))
          
          ;; Handle string delimiters
          (when (and (eq ch #\") (not escape-next))
            (setf in-string (not in-string)))
          
          ;; Handle escapes
          (setf escape-next (and (not escape-next) (eq ch #\\)))
          
          ;; Check for top-level terminators
          (when (and (zerop depth) (not in-string) (not escape-next))
            (cond
              ;; Line comment
              ((eq ch #\;) (return))
              ;; Block comment
              ((and (eq ch #\#) 
                    (eq (peek-char t stream nil) #\|))
               (return))
              ;; Whitespace at top level
              ((member ch '(#\Space #\Tab #\Newline #\Return #\Page))
               (return))))
          
          ;; Track parenthesis depth (outside strings)
          (unless in-string
            (cond 
              ((eq ch #\() (incf depth))
              ((eq ch #\)) 
               (if (> depth 0)
                   (decf depth)
                   (return))))) ; unmatched ), stop
          
          ;; Accumulate character
          (write-char (read-char stream) out))))))

(defun next-item (stream)
  "Read next item (form or comment) from stream. Returns (type . source) or nil."
  (skip-whitespace stream)
  (let ((ch (peek-char nil stream nil)))
    (cond
      ;; EOF
      ((null ch) nil)
      
      ;; Line comment
      ((eq ch #\;)
       (cons :comment (read-line-comment stream)))
      
      ;; Block comment
      ((and (eq ch #\#) 
            (eq (peek-char t stream nil) #\|))
       (cons :comment (read-block-comment stream)))
      
      ;; Form
      (t
       (let ((source (read-form-source stream)))
         (when (and source (> (length source) 0))
           (cons :form source)))))))

(defun read-all-items (stream)
  "Read all items from stream. Returns list of (type . source) pairs."
  (loop for item = (next-item stream)
        while item
        collect item))

;;;; Notebook Generation

(defun make-code-cell (source)
  "Create a code cell alist."
  `(("cell_type" . "code")
    ("execution_count" . :null)
    ("metadata" . ())
    ("outputs" . ())
    ("source" . (,source))))

(defun make-raw-cell (source)
  "Create a raw cell alist for comments."
  `(("cell_type" . "raw")
    ("metadata" . (("format" . "text/plain")))
    ("source" . (,(concatenate 'string "; " source)))))

(defun make-notebook (cells)
  "Create notebook structure alist."
  `(("nbformat" . 4)
    ("nbformat_minor" . 2)
    ("metadata" . (("kernelspec" . (("display_name" . "SBCL")
                                     ("language" . "lisp")
                                     ("name" . "sbcl")))
                   ("language_info" . (("name" . "common-lisp")
                                       ("version" . "SBCL")
                                       ("mimetype" . "text/x-lisp")
                                       ("file_extension" . ".lisp")))))
    ("cells" . ,cells)))

(defun items-to-cells (items)
  "Convert items to notebook cells."
  (loop for (type . source) in items
        collect (ecase type
                  (:form (make-code-cell source))
                  (:comment (make-raw-cell source)))))

;;;; Main Conversion

(defun convert-file (input-file output-file)
  "Convert Lisp file to Jupyter notebook."
  (with-open-file (in input-file :direction :input)
    (let* ((items (read-all-items in))
           (cells (items-to-cells items))
           (notebook (make-notebook cells)))
      
      (with-open-file (out output-file 
                          :direction :output 
                          :if-exists :supersede
                          :if-does-not-exist :create)
        (write-json-object notebook out :newlines t :indent 2)
        (terpri out))
      
      (format *error-output* "[+] Converted ~A items to ~A~%" 
              (length items) output-file))))

;;;; Command-line Interface

(defun main ()
  (let ((args (rest *posix-argv*)))
    (cond
      ((< (length args) 2)
       (format *error-output* "Usage: sbcl --script lisp2ipynb.lisp <input.lisp> <output.ipynb>~%")
       (format *error-output* "~%")
       (format *error-output* "Converts SBCL/ACL2 Lisp files to Jupyter notebooks.~%")
       (format *error-output* "Forms → code cells, Comments → raw cells.~%")
       (format *error-output* "Syntactic parsing only (no interning, no package resolution).~%")
       (sb-ext:exit :code 1))
      
      (t
       (let ((input (first args))
             (output (second args)))
         (handler-case
             (progn
               (convert-file input output)
               (sb-ext:exit :code 0))
           (error (e)
             (format *error-output* "ERROR: ~A~%" e)
             (sb-ext:exit :code 1))))))))

(main)
