;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-

; HTTP JSON Client -- Raw Lisp Implementation
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance
;
; This file provides the raw Lisp implementation for JSON HTTP POST requests.
; It uses Dexador directly with proper error handling.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; post-json implementation
;;
;; Makes HTTP POST request with JSON body.
;; Returns (mv error-string body-string status-code state)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post-json (url json-body headers connect-timeout read-timeout state)
  (if (not (live-state-p state))
      (prog2$ (error "POST-JSON can only be called on a live state.")
              (mv "ERROR: not live state" "" 0 state))
    (if (not (stringp url))
        (prog2$ (error "POST-JSON called with non-stringp url")
                (mv "ERROR: url not string" "" 0 state))
      (if (not (stringp json-body))
          (prog2$ (error "POST-JSON called with non-stringp json-body")
                  (mv "ERROR: json-body not string" "" 0 state))
        (handler-case
            (multiple-value-bind (body status response-headers uri stream)
                (dex:post url 
                          :content json-body
                          :headers headers
                          :connect-timeout connect-timeout
                          :read-timeout read-timeout)
              (declare (ignore response-headers uri stream))
              ;; Return success: nil error, body, status, state
              (mv nil (if (stringp body) body "") status state))
          
          (error (condition)
                 (let ((condition-str (format nil "~a" condition)))
                   (mv condition-str "" 0 state))))))))

