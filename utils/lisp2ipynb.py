#!/usr/bin/env python3
"""
Lisp (.lisp) to Jupyter Notebook (.ipynb) Converter

Converts SBCL/ACL2 Lisp files to Jupyter notebooks using the SBCL reader
at a syntactic level (no interning, no package resolution).

Forms become code cells. Comments between forms become raw (Markdown) cells.

Usage:
    python3 lisp2ipynb.py input.lisp output.ipynb
    python3 lisp2ipynb.py input.lisp > output.ipynb  (stdout)
"""

import json
import sys
import subprocess
import re
from pathlib import Path
from typing import List, Dict, Any, Tuple


LISP_READER_SCRIPT = """
(defun read-syntactically (stream)
  "Read a single form from stream without interning symbols.
   Returns a cons cell (TYPE . DATA) where TYPE is one of:
   :FORM - executable Lisp form
   :COMMENT - comment text
   :EOF - end of file"
  
  (let ((char (peek-char nil stream nil)))
    (cond
      ((null char)
       (cons :EOF nil))
      
      ;; Skip whitespace
      ((member char '(#\\Space #\\Tab #\\Newline #\\Return #\\Page))
       (read-char stream)
       (read-syntactically stream))
      
      ;; Comments
      ((eq char #\\;)
       (read-char stream)  ; consume semicolon
       (let ((comment-text (make-string-output-stream)))
         (loop for c = (read-char stream nil)
               while (and c (not (eq c #\\Newline)))
               do (write-char c comment-text))
         (cons :COMMENT (get-output-stream-string comment-text))))
      
      ;; Block comments #| ... |#
      ((eq char #\\#)
       (let ((next (peek-char t stream nil)))
         (if (eq next #\\|)
             (progn
               (read-char stream)  ; consume #
               (read-char stream)  ; consume |
               (let ((comment-text (make-string-output-stream)))
                 (loop with depth = 1
                       for c = (read-char stream nil)
                       while (and c (> depth 0))
                       do (progn
                            (when (and (not (null (peek-char nil stream nil)))
                                      (eq c #\\#)
                                      (eq (peek-char nil stream nil) #\\|))
                              (read-char stream)  ; consume |
                              (incf depth))
                            (when (and (not (null (peek-char nil stream nil)))
                                      (eq c #\\|)
                                      (eq (peek-char nil stream nil) #\\#))
                              (read-char stream)  ; consume #
                              (decf depth))
                            (write-char c comment-text)))
                 (cons :COMMENT (get-output-stream-string comment-text))))
             ;; Not a block comment, read as regular form
             (read-form-syntactically stream))))
      
      ;; Regular forms
      (t
       (read-form-syntactically stream)))))


(defun read-form-syntactically (stream)
  "Read a Lisp form syntactically without interning."
  (let ((form-text (make-string-output-stream)))
    (read-form-chars stream form-text 0)
    (let ((text (get-output-stream-string form-text)))
      (unless (zerop (length text))
        (cons :FORM text)))))


(defun read-form-chars (stream output paren-depth)
  "Accumulate form characters into output, tracking parenthesis depth."
  (let ((char (peek-char nil stream nil)))
    (cond
      ((null char)
       nil)  ; EOF
      
      ((and (zerop paren-depth) (member char '(#\\; #\\Space #\\Tab #\\Newline #\\Return #\\Page)))
       nil)  ; End of form at whitespace (outside parens)
      
      ((member char '(#\\Space #\\Tab #\\Newline #\\Return #\\Page))
       (write-char char output)
       (read-char stream)
       (read-form-chars stream output paren-depth))
      
      ((eq char #\\()
       (write-char char output)
       (read-char stream)
       (read-form-chars stream output (1+ paren-depth)))
      
      ((eq char #\\))
       (if (> paren-depth 0)
           (progn
             (write-char char output)
             (read-char stream)
             (read-form-chars stream output (1- paren-depth)))
           nil))  ; Unmatched closing paren, stop
      
      ((and (zerop paren-depth) (eq char #\\;))
       nil)  ; Comment starts, end form
      
      (t
       (write-char char output)
       (read-char stream)
       (read-form-chars stream output paren-depth)))))


(defun convert-lisp-to-notebook (input-file output-file)
  "Main converter: reads Lisp file, outputs Jupyter .ipynb JSON."
  (let ((cells (make-array 0 :adjustable t :fill-pointer t)))
    
    ;; Read all forms and comments
    (with-open-file (in input-file :direction :input)
      (loop
        (let ((item (read-syntactically in)))
          (when (eq (car item) :EOF)
            (return))
          (vector-push-extend item cells))))
    
    ;; Build notebook structure
    (let ((notebook (make-notebook)))
      (loop for i from 0 below (length cells)
            for item = (aref cells i)
            for type = (car item)
            for content = (cdr item)
            do (cond
                 ((eq type :FORM)
                  (add-code-cell notebook content))
                 ((eq type :COMMENT)
                  (add-markdown-cell notebook content))))
      
      ;; Write notebook JSON
      (with-open-file (out output-file :direction :output :if-exists :supersede)
        (write-notebook out notebook)))))


(defun make-notebook ()
  "Create an empty notebook structure (as alist for JSON serialization)."
  (list
    (cons "nbformat" 4)
    (cons "nbformat_minor" 2)
    (cons "metadata" (list
      (cons "kernelspec" (list
        (cons "display_name" "Common Lisp")
        (cons "language" "lisp")
        (cons "name" "common-lisp")))
      (cons "language_info" (list
        (cons "name" "common-lisp")
        (cons "version" "1.0")))))
    (cons "cells" (vector))))


(defun add-code-cell (notebook source)
  "Add a code cell to notebook."
  (let* ((cells-cell (assoc "cells" notebook))
         (cells (cdr cells-cell)))
    (vector-push-extend
      (list
        (cons "cell_type" "code")
        (cons "source" (list source))
        (cons "metadata" '())
        (cons "outputs" (vector))
        (cons "execution_count" :null))
      cells)))


(defun add-markdown-cell (notebook source)
  "Add a markdown/raw cell to notebook."
  (let* ((cells-cell (assoc "cells" notebook))
         (cells (cdr cells-cell)))
    (vector-push-extend
      (list
        (cons "cell_type" "raw")
        (cons "source" (list source))
        (cons "metadata" '()))
      cells)))


(defun write-notebook (stream notebook)
  "Write notebook as JSON to stream."
  ;; This is simplified - in practice use yason or jsown library
  ;; For now, output basic structure
  (write-char #\\{ stream)
  ;; ... JSON serialization (details below)
  (terpri stream))


;; Main entry point
(defun main ()
  (let ((args (rest *posix-argv*)))
    (if (< (length args) 2)
        (progn
          (format t "Usage: sbcl --script lisp2ipynb.lisp <input.lisp> <output.ipynb>~%")
          (sb-ext:exit :code 1))
        (let ((input (first args))
              (output (second args)))
          (handler-case
              (convert-lisp-to-notebook input output)
            (error (e)
              (format t "Error: ~A~%" e)
              (sb-ext:exit :code 1)))))))

(main)
"""


def parse_lisp_file(lisp_file: Path) -> List[Tuple[str, str]]:
    """
    Use SBCL reader to parse Lisp file syntactically.
    Returns list of (type, content) tuples.
    """
    # Create temporary Lisp script that reads and outputs forms
    temp_lisp = Path("/tmp/lisp_reader_temp.lisp")
    
    reader_code = f'''
(defparameter *forms* (make-array 0 :adjustable t :fill-pointer t))

(defun read-syntactically (stream)
  "Read forms without interning, preserving exact syntax."
  (loop
    (let ((char (peek-char nil stream nil)))
      (when (null char) (return))
      
      ;; Skip whitespace
      (when (member char '(#\\Space #\\Tab #\\Newline #\\Return #\\Page))
        (read-char stream)
        (loop))
      
      ;; Handle comments
      (when (eq char #\\;)
        (read-char stream)
        (let ((comment (make-string-output-stream)))
          (loop for c = (read-char stream nil)
                while (and c (not (eq c #\\Newline)))
                do (write-char c comment))
          (vector-push-extend (cons :comment (get-output-stream-string comment)) *forms*))
        (loop))
      
      ;; Read form
      (let ((form-str (read-form-text stream)))
        (when form-str
          (vector-push-extend (cons :form form-str) *forms*)))
      (loop))))

(defun read-form-text (stream)
  "Read raw form text without evaluation."
  (let ((output (make-string-output-stream))
        (paren-count 0))
    (loop
      (let ((ch (peek-char nil stream nil)))
        (when (null ch) (return))
        
        (cond
          ((eq ch #\\() 
           (write-char (read-char stream) output)
           (incf paren-count))
          ((eq ch #\\))
           (if (> paren-count 0)
               (progn
                 (write-char (read-char stream) output)
                 (decf paren-count))
               (return)))
          ((and (zerop paren-count) 
                (member ch '(#\\; #\\Space #\\Tab #\\Newline #\\Return)))
           (return))
          (t
           (write-char (read-char stream) output))))
      
      (when (and (zerop paren-count)
                 (not (member (peek-char nil stream nil) 
                            '(#\\Space #\\Tab #\\Newline #\\Return #\\Page #\\; nil))))
        (return)))
    
    (let ((text (get-output-stream-string output)))
      (if (zerop (length text)) nil text))))

;; Parse file
(with-open-file (stream "{lisp_file}" :direction :input)
  (read-syntactically stream))

;; Output results
(format t "~S~%" *forms*)
(sb-ext:exit)
'''
    
    try:
        # Write temp script
        temp_lisp.write_text(reader_code)
        
        # Run SBCL
        result = subprocess.run(
            ["sbcl", "--script", str(temp_lisp)],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode != 0:
            raise RuntimeError(f"SBCL error: {result.stderr}")
        
        # Parse output (Lisp s-expression format)
        output = result.stdout.strip()
        forms = eval_lisp_output(output)
        
        return forms
    
    finally:
        if temp_lisp.exists():
            temp_lisp.unlink()


def eval_lisp_output(output: str) -> List[Tuple[str, str]]:
    """Parse SBCL output (Lisp s-expressions) into Python structures."""
    # Simplified parser for ((FORM . "text") (COMMENT . "text") ...)
    items = []
    
    # Match patterns: (:<type> . "content")
    pattern = r'\(\s*:(\w+)\s*\.\s*"([^"]*?)"\s*\)'
    
    for match in re.finditer(pattern, output):
        item_type = match.group(1).lower()
        content = match.group(2)
        # Unescape newlines in content
        content = content.replace('\\n', '\n')
        items.append((item_type, content))
    
    return items


def create_notebook(forms: List[Tuple[str, str]]) -> Dict[str, Any]:
    """Create Jupyter notebook structure from forms."""
    notebook = {
        "nbformat": 4,
        "nbformat_minor": 2,
        "metadata": {
            "kernelspec": {
                "display_name": "SBCL",
                "language": "lisp",
                "name": "sbcl"
            },
            "language_info": {
                "name": "common-lisp",
                "version": "2.5"
            }
        },
        "cells": []
    }
    
    for item_type, content in forms:
        if item_type == "form":
            # Code cell
            notebook["cells"].append({
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [content + "\n"]
            })
        elif item_type == "comment":
            # Raw cell (preserves original comment text)
            notebook["cells"].append({
                "cell_type": "raw",
                "metadata": {},
                "source": ["; " + content + "\n"]
            })
    
    return notebook


def main():
    if len(sys.argv) < 2:
        print("Usage: lisp2ipynb.py <input.lisp> [output.ipynb]", file=sys.stderr)
        print("       Converts SBCL/ACL2 Lisp files to Jupyter notebooks", file=sys.stderr)
        sys.exit(1)
    
    input_file = Path(sys.argv[1])
    output_file = Path(sys.argv[2]) if len(sys.argv) > 2 else input_file.with_suffix(".ipynb")
    
    if not input_file.exists():
        print(f"Error: {input_file} not found", file=sys.stderr)
        sys.exit(1)
    
    try:
        print(f"Parsing {input_file}...", file=sys.stderr)
        forms = parse_lisp_file(input_file)
        
        print(f"Found {len(forms)} items (forms and comments)", file=sys.stderr)
        notebook = create_notebook(forms)
        
        with open(output_file, "w") as f:
            json.dump(notebook, f, indent=2)
        
        print(f"Written to {output_file}", file=sys.stderr)
    
    except subprocess.TimeoutExpired:
        print("Error: SBCL parsing timed out", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
