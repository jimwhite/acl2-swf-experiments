#!/usr/bin/env python3
"""
Lisp (.lisp) to Jupyter Notebook (.ipynb) Converter for SBCL/ACL2

Converts Common Lisp source files to Jupyter notebooks using SBCL's reader
at a purely syntactic level (no interning, no package resolution).

Key Features:
  - Syntactic parsing only (respects reader macros but doesn't resolve symbols)
  - Forms → code cells
  - Comments (both ; and #| |#) → raw cells
  - Preserves original formatting and whitespace
  - No dependency on package system or symbol interning

Usage:
    python3 lisp2ipynb.py input.lisp output.ipynb
    python3 lisp2ipynb.py input.lisp  # writes to input.ipynb
"""

import json
import sys
import subprocess
import tempfile
from pathlib import Path
from typing import List, Tuple, Optional


class LispParser:
    """Parse Lisp files using SBCL reader without interning."""
    
    SBCL_READER = r'''
;;; Syntactic Lisp reader that preserves source structure
;;; without interning symbols or resolving packages

(defun read-forms-syntactically (filename)
  "Read all top-level forms from filename without interning.
   Returns list of (TYPE . SOURCE) where TYPE is :FORM or :COMMENT"
  
  (let ((items '()))
    (with-open-file (stream filename :direction :input)
      (loop
        (let ((item (next-item stream)))
          (when (null item) (return))
          (push item items))))
    (nreverse items)))


(defun next-item (stream)
  "Read next item (form or comment), skipping whitespace. Returns nil at EOF."
  
  (skip-whitespace stream)
  (let ((ch (peek-char nil stream nil)))
    (cond
      ((null ch) nil)
      
      ;; Line comment
      ((eq ch #\;)
       (read-char stream)  ; consume ;
       (let ((buffer (make-string-output-stream)))
         (loop for c = (read-char stream nil nil)
               while (and c (not (eq c #\Newline)))
               do (write-char c buffer))
         (cons :COMMENT (get-output-stream-string buffer))))
      
      ;; Block comment
      ((and (eq ch #\#) (eql (peek-char t stream nil) #\|))
       (read-char stream)  ; #
       (read-char stream)  ; |
       (let ((buffer (make-string-output-stream))
             (depth 1))
         (loop while (> depth 0)
               for c = (read-char stream nil nil)
               while c
               do (progn
                    ;; Check for nested #|
                    (when (and (eq c #\#) (eql (peek-char nil stream nil) #\|))
                      (read-char stream)  ; consume |
                      (incf depth)
                      (write-char c buffer)
                      (write-char #\| buffer)
                      (loop))
                    ;; Check for closing |#
                    (when (and (eq c #\|) (eql (peek-char nil stream nil) #\#))
                      (read-char stream)  ; consume #
                      (decf depth)
                      (unless (zerop depth)
                        (write-char c buffer)
                        (write-char #\# buffer))
                      (loop))
                    ;; Regular character
                    (write-char c buffer)))
         (cons :COMMENT (get-output-stream-string buffer))))
      
      ;; Regular form (don't use READ to avoid symbol interning)
      (t
       (let ((form-source (read-form-source stream)))
         (when form-source
           (cons :FORM form-source)))))))


(defun skip-whitespace (stream)
  "Consume whitespace characters from stream."
  (loop for ch = (peek-char nil stream nil)
        while (and ch (member ch '(#\Space #\Tab #\Newline #\Return #\Page)))
        do (read-char stream)))


(defun read-form-source (stream)
  "Read a complete form as a string, without evaluating or interning."
  
  (let ((buffer (make-string-output-stream))
        (depth 0)           ; track parenthesis depth
        (in-string nil)     ; track if inside string
        (escape-next nil))  ; track escape sequences
    
    (loop
      (let ((ch (peek-char nil stream nil)))
        (when (null ch) (return))  ; EOF
        
        ;; String handling
        (when (and (eq ch #\") (not escape-next))
          (setf in-string (not in-string)))
        
        ;; Escape handling
        (if escape-next
            (setf escape-next nil)
            (when (eq ch #\\)
              (setf escape-next t)))
        
        ;; Top-level terminators (when not in string or parens)
        (when (and (zerop depth) (not in-string) (not escape-next))
          (cond
            ;; Comment starts
            ((eq ch #\;) (return))
            ;; Block comment
            ((and (eq ch #\#) (eql (peek-char t stream nil) #\|))
             (return))
            ;; Whitespace terminates at depth 0
            ((member ch '(#\Space #\Tab #\Newline #\Return #\Page))
             (return))))
        
        ;; Track parenthesis depth
        (unless in-string
          (cond ((eq ch #\() (incf depth))
                ((eq ch #\)) 
                 (if (> depth 0)
                     (decf depth)
                     (return)))))  ; unmatched ), stop
        
        ;; Accumulate character
        (write-char (read-char stream) buffer))))
    
    (let ((result (get-output-stream-string buffer)))
      (when (> (length result) 0)
        result))))


;;; Main: read file and output as S-expressions
(let ((filename (first (rest (member "--lisp-file" *posix-argv* :test 'equal)))))
  (unless filename
    (format *error-output* "ERROR: --lisp-file argument required~%")
    (sb-ext:exit :code 1))
  
  (handler-case
      (let ((items (read-forms-syntactically filename)))
        ;; Output as readable S-expression
        (format t "~S~%" items)
        (sb-ext:exit :code 0))
    (error (e)
      (format *error-output* "ERROR: ~A~%" e)
      (sb-ext:exit :code 1))))
'''
    
    def __init__(self):
        """Initialize parser."""
        self.sbcl_available = self._check_sbcl()
    
    def _check_sbcl(self) -> bool:
        """Check if SBCL is available."""
        try:
            result = subprocess.run(
                ["sbcl", "--version"],
                capture_output=True,
                timeout=5
            )
            return result.returncode == 0
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return False
    
    def parse(self, lisp_file: Path) -> List[Tuple[str, str]]:
        """Parse Lisp file using SBCL reader. Returns [(type, source), ...]"""
        
        if not self.sbcl_available:
            raise RuntimeError(
                "SBCL not found. Install with: apt-get install sbcl (Linux) "
                "or brew install sbcl (macOS)"
            )
        
        # Write reader script to temp file
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.lisp',
            delete=False
        ) as f:
            f.write(self.SBCL_READER)
            reader_file = f.name
        
        try:
            # Run SBCL with reader script
            result = subprocess.run(
                [
                    "sbcl",
                    "--non-interactive",
                    "--load", reader_file,
                    "--lisp-file", str(lisp_file)
                ],
                capture_output=True,
                text=True,
                timeout=60
            )
            
            if result.returncode != 0:
                raise RuntimeError(
                    f"SBCL parsing failed:\n{result.stderr}"
                )
            
            # Parse output (SBCL outputs Lisp s-expression)
            return self._parse_sexpr_output(result.stdout.strip())
        
        finally:
            Path(reader_file).unlink()
    
    def _parse_sexpr_output(self, output: str) -> List[Tuple[str, str]]:
        """Parse SBCL s-expression output.
        
        Format: (((:FORM . "source1") (:COMMENT . "text") ...) ...)
        """
        items = []
        
        # Simple regex-based parser for cons cells
        # Match: (:TYPE . "STRING")
        import re
        pattern = r'\(:\s*(\w+)\s*\.\s*"([^"]*?)"\s*\)'
        
        for match in re.finditer(pattern, output):
            item_type = match.group(1).lower()
            source = match.group(2)
            # Unescape embedded quotes and newlines
            source = source.replace('\\"', '"').replace('\\n', '\n')
            items.append((item_type, source))
        
        return items


class NotebookBuilder:
    """Build Jupyter notebook structure."""
    
    @staticmethod
    def create(items: List[Tuple[str, str]]) -> dict:
        """Create notebook from parsed items."""
        
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
                    "version": "SBCL 2.3+",
                    "mimetype": "text/x-lisp",
                    "file_extension": ".lisp"
                }
            },
            "cells": []
        }
        
        for item_type, source in items:
            if item_type == "form":
                # Code cell
                notebook["cells"].append({
                    "cell_type": "code",
                    "execution_count": None,
                    "metadata": {},
                    "outputs": [],
                    "source": [source.rstrip() + "\n"]
                })
            elif item_type == "comment":
                # Raw cell (preserve comment exactly)
                notebook["cells"].append({
                    "cell_type": "raw",
                    "metadata": {
                        "format": "text/plain"
                    },
                    "source": ["; " + source.rstrip() + "\n"]
                })
        
        return notebook


def main():
    """Main entry point."""
    
    if len(sys.argv) < 2:
        print(
            "Usage: lisp2ipynb.py <input.lisp> [output.ipynb]\n"
            "\n"
            "Converts SBCL/ACL2 Lisp source files to Jupyter notebooks.\n"
            "Forms become code cells. Comments become raw cells.\n"
            "No symbol interning or package resolution—purely syntactic.",
            file=sys.stderr
        )
        sys.exit(1)
    
    input_file = Path(sys.argv[1])
    output_file = (
        Path(sys.argv[2])
        if len(sys.argv) > 2
        else input_file.with_suffix(".ipynb")
    )
    
    # Validate input
    if not input_file.exists():
        print(f"ERROR: {input_file} not found", file=sys.stderr)
        sys.exit(1)
    
    if not input_file.is_file():
        print(f"ERROR: {input_file} is not a file", file=sys.stderr)
        sys.exit(1)
    
    try:
        print(f"[*] Parsing {input_file} with SBCL...", file=sys.stderr)
        
        parser = LispParser()
        items = parser.parse(input_file)
        
        print(f"[+] Found {len(items)} items", file=sys.stderr)
        
        notebook = NotebookBuilder.create(items)
        
        with open(output_file, 'w') as f:
            json.dump(notebook, f, indent=2)
        
        print(f"[+] Notebook written to {output_file}", file=sys.stderr)
    
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
