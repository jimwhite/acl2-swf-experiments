; HTTP JSON Client -- Properly-guarded JSON POST for ACL2
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance
;
; This book provides a properly-guarded post-json function that accepts
; stringp JSON body (unlike kestrel/htclient/post-light which requires alistp).
; This follows the oracle model for network I/O in formal verification.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "quicklisp/dexador" :dir :system)
; (depends-on "http-json-raw.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper: state preservation theorem for oracle reads
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm state-p1-of-read-acl2-oracle
   (implies (state-p1 state)
            (state-p1 (mv-nth 2 (read-acl2-oracle state))))
   :hints (("Goal" :in-theory (enable read-acl2-oracle)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; post-json: HTTP POST with JSON string body
;;
;; This is the logical specification. The raw Lisp implementation in
;; http-json-raw.lsp replaces this with actual Dexador calls.
;;
;; Parameters:
;;   url           - Target URL (stringp)
;;   json-body     - JSON request body as string (stringp)
;;   headers       - HTTP headers as alist (alistp)
;;   connect-timeout - Connection timeout in seconds (natp)
;;   read-timeout  - Read timeout in seconds (natp)
;;   state         - ACL2 state
;;
;; Returns: (mv error body status state)
;;   error  - NIL on success, error string on failure
;;   body   - Response body as string
;;   status - HTTP status code (0 on error)
;;   state  - Updated state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post-json (url json-body headers connect-timeout read-timeout state)
  (declare (xargs :guard (and (stringp url)
                              (stringp json-body)
                              (alistp headers)
                              (natp connect-timeout)
                              (natp read-timeout))
                  :stobjs state)
           (ignore url json-body headers connect-timeout read-timeout))
  ;; Logical definition reads from oracle (will be replaced by raw Lisp)
  (prog2$ 
   (er hard? 'post-json "Raw Lisp definition not installed?")
   (mv-let (err1 val1 state)
     (read-acl2-oracle state)
     (declare (ignore err1))
     (mv-let (err2 val2 state)
       (read-acl2-oracle state)
       (declare (ignore err2))
       (mv-let (err3 val3 state)
         (read-acl2-oracle state)
         (declare (ignore err3))
         ;; Return: error (or nil), body string, status code
         (mv (if (stringp val1) val1 nil)
             (if (stringp val2) val2 "")
             (if (natp val3) val3 0)
             state))))))

;; Return type theorems
(defthm stringp-or-null-of-post-json-error
  (or (null (mv-nth 0 (post-json url json-body headers ct rt state)))
      (stringp (mv-nth 0 (post-json url json-body headers ct rt state))))
  :rule-classes (:rewrite :type-prescription))

(defthm stringp-of-post-json-body
  (stringp (mv-nth 1 (post-json url json-body headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-of-post-json-status
  (natp (mv-nth 2 (post-json url json-body headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm state-p1-of-post-json
  (implies (state-p1 state)
           (state-p1 (mv-nth 3 (post-json url json-body headers ct rt state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; post-json-with-headers: HTTP POST returning response headers
;;
;; Like post-json but also returns response headers as alist.
;; Needed for MCP protocol which returns session ID in headers.
;;
;; Parameters:
;;   url           - Target URL (stringp)
;;   json-body     - JSON request body as string (stringp)
;;   headers       - HTTP headers as alist (alistp)
;;   connect-timeout - Connection timeout in seconds (natp)
;;   read-timeout  - Read timeout in seconds (natp)
;;   state         - ACL2 state
;;
;; Returns: (mv error body status response-headers state)
;;   error   - NIL on success, error string on failure
;;   body    - Response body as string
;;   status  - HTTP status code (0 on error)
;;   response-headers - Response headers as alist
;;   state   - Updated state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post-json-with-headers (url json-body headers connect-timeout read-timeout state)
  (declare (xargs :guard (and (stringp url)
                              (stringp json-body)
                              (alistp headers)
                              (natp connect-timeout)
                              (natp read-timeout))
                  :stobjs state)
           (ignore url json-body headers connect-timeout read-timeout))
  ;; Logical definition reads from oracle (will be replaced by raw Lisp)
  (prog2$ 
   (er hard? 'post-json-with-headers "Raw Lisp definition not installed?")
   (mv-let (err1 val1 state)
     (read-acl2-oracle state)
     (declare (ignore err1))
     (mv-let (err2 val2 state)
       (read-acl2-oracle state)
       (declare (ignore err2))
       (mv-let (err3 val3 state)
         (read-acl2-oracle state)
         (declare (ignore err3))
         (mv-let (err4 val4 state)
           (read-acl2-oracle state)
           (declare (ignore err4))
           ;; Return: error (or nil), body string, status code, headers alist
           (mv (if (stringp val1) val1 nil)
               (if (stringp val2) val2 "")
               (if (natp val3) val3 0)
               (if (alistp val4) val4 nil)
               state)))))))

;; Return type theorems for post-json-with-headers
(defthm stringp-or-null-of-post-json-with-headers-error
  (or (null (mv-nth 0 (post-json-with-headers url json-body headers ct rt state)))
      (stringp (mv-nth 0 (post-json-with-headers url json-body headers ct rt state))))
  :rule-classes (:rewrite :type-prescription))

(defthm stringp-of-post-json-with-headers-body
  (stringp (mv-nth 1 (post-json-with-headers url json-body headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-of-post-json-with-headers-status
  (natp (mv-nth 2 (post-json-with-headers url json-body headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm alistp-of-post-json-with-headers-response-headers
  (alistp (mv-nth 3 (post-json-with-headers url json-body headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm state-p1-of-post-json-with-headers
  (implies (state-p1 state)
           (state-p1 (mv-nth 4 (post-json-with-headers url json-body headers ct rt state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get-json: HTTP GET for JSON endpoints
;;
;; Parameters:
;;   url           - Target URL (stringp)
;;   headers       - HTTP headers as alist (alistp)
;;   connect-timeout - Connection timeout in seconds (natp)
;;   read-timeout  - Read timeout in seconds (natp)
;;   state         - ACL2 state
;;
;; Returns: (mv error body status state)
;;   error  - NIL on success, error string on failure
;;   body   - Response body as string
;;   status - HTTP status code (0 on error)
;;   state  - Updated state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-json (url headers connect-timeout read-timeout state)
  (declare (xargs :guard (and (stringp url)
                              (alistp headers)
                              (natp connect-timeout)
                              (natp read-timeout))
                  :stobjs state)
           (ignore url headers connect-timeout read-timeout))
  ;; Logical definition reads from oracle (will be replaced by raw Lisp)
  (prog2$ 
   (er hard? 'get-json "Raw Lisp definition not installed?")
   (mv-let (err1 val1 state)
     (read-acl2-oracle state)
     (declare (ignore err1))
     (mv-let (err2 val2 state)
       (read-acl2-oracle state)
       (declare (ignore err2))
       (mv-let (err3 val3 state)
         (read-acl2-oracle state)
         (declare (ignore err3))
         ;; Return: error (or nil), body string, status code
         (mv (if (stringp val1) val1 nil)
             (if (stringp val2) val2 "")
             (if (natp val3) val3 0)
             state))))))

;; Return type theorems for get-json
(defthm stringp-of-get-json-body
  (stringp (mv-nth 1 (get-json url headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-of-get-json-status
  (natp (mv-nth 2 (get-json url headers ct rt state)))
  :rule-classes (:rewrite :type-prescription))

(defthm state-p1-of-get-json
  (implies (state-p1 state)
           (state-p1 (mv-nth 3 (get-json url headers ct rt state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trust tag and raw Lisp inclusion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :http-json)
(include-raw "http-json-raw.lsp"
             :host-readtable t)

