; LLM Types -- FTY type definitions for LLM chat messages
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; Author: AI Assistant with human guidance

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Chat Role
;;
;; Represents the role of a message in a chat conversation.
;; OpenAI-compatible roles for LLM APIs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum chat-role
  (:system ())      ; System prompt / instructions
  (:user ())        ; User input
  (:assistant ())   ; Model response
  (:tool ()))       ; Tool result (for future MCP integration)

;; Helper functions for creating roles
(defmacro role-system () '(chat-role-system))
(defmacro role-user () '(chat-role-user))
(defmacro role-assistant () '(chat-role-assistant))
(defmacro role-tool () '(chat-role-tool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Chat Message
;;
;; A single message in a conversation with role and content.
;; Future extension: add tool-calls and tool-call-id for MCP.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod chat-message
  ((role chat-role-p "The role of the message sender")
   (content stringp "The text content of the message" :default ""))
  :layout :list)

;; Convenient constructors
(define make-system-message ((content stringp))
  :returns (msg chat-message-p)
  (make-chat-message :role (role-system) :content content))

(define make-user-message ((content stringp))
  :returns (msg chat-message-p)
  (make-chat-message :role (role-user) :content content))

(define make-assistant-message ((content stringp))
  :returns (msg chat-message-p)
  (make-chat-message :role (role-assistant) :content content))

(define make-tool-message ((content stringp))
  :returns (msg chat-message-p)
  (make-chat-message :role (role-tool) :content content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Chat Message List
;;
;; A list of messages representing a conversation history.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist chat-message-list
  :elt-type chat-message-p
  :true-listp t)

;; Utility: Check if conversation has a system message
(define has-system-message-p ((messages chat-message-list-p))
  :returns (has booleanp)
  (if (endp messages)
      nil
    (let ((role (chat-message->role (car messages))))
      (or (chat-role-case role :system t :otherwise nil)
          (has-system-message-p (cdr messages))))))

;; Utility: Get the last assistant message content (if any)
(define last-assistant-content ((messages chat-message-list-p))
  :returns (content stringp)
  (if (endp messages)
      ""
    (let* ((msg (car (last messages)))
           (role (chat-message->role msg)))
      (if (chat-role-case role :assistant t :otherwise nil)
          (chat-message->content msg)
        ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Role to String Conversion (for JSON serialization)
;;
;; These are pure ACL2 functions - the raw Lisp code will use them.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chat-role-to-string ((role chat-role-p))
  :returns (s stringp)
  (chat-role-case role
    :system "system"
    :user "user"
    :assistant "assistant"
    :tool "tool"))

(define string-to-chat-role ((s stringp))
  :returns (role chat-role-p)
  (cond ((equal s "system") (role-system))
        ((equal s "user") (role-user))
        ((equal s "assistant") (role-assistant))
        ((equal s "tool") (role-tool))
        ;; Default to user for unknown roles
        (t (role-user))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic Theorems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm chat-role-to-string-returns-valid-string
  (implies (chat-role-p role)
           (member-equal (chat-role-to-string role)
                        '("system" "user" "assistant" "tool")))
  :hints (("Goal" :in-theory (enable chat-role-to-string))))

(defthm string-to-chat-role-roundtrip
  (implies (and (stringp s)
                (member-equal s '("system" "user" "assistant" "tool")))
           (equal (chat-role-to-string (string-to-chat-role s)) s))
  :hints (("Goal" :in-theory (enable chat-role-to-string string-to-chat-role))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Model Type
;;
;; Type of model: llm (chat/completion), vlm (vision), embeddings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum model-type
  (:llm ())         ; Language model for chat/completion
  (:vlm ())         ; Vision-language model
  (:embeddings ())) ; Embedding model

(define model-type-to-string ((mt model-type-p))
  :returns (s stringp)
  (model-type-case mt
    :llm "llm"
    :vlm "vlm"
    :embeddings "embeddings"))

(define string-to-model-type ((s stringp))
  :returns (mt model-type-p)
  (cond ((equal s "llm") (model-type-llm))
        ((equal s "vlm") (model-type-vlm))
        ((equal s "embeddings") (model-type-embeddings))
        ;; Default to llm for unknown
        (t (model-type-llm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Model State
;;
;; Whether a model is loaded into memory or not
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum model-state
  (:loaded ())
  (:not-loaded ()))

(define model-state-to-string ((ms model-state-p))
  :returns (s stringp)
  (model-state-case ms
    :loaded "loaded"
    :not-loaded "not-loaded"))

(define string-to-model-state ((s stringp))
  :returns (ms model-state-p)
  (if (equal s "loaded")
      (model-state-loaded)
    (model-state-not-loaded)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Model Info
;;
;; Full information about a model from LM Studio /api/v0/models
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod model-info
  ((id stringp "Model identifier" :default "")
   (type model-type-p "Type: llm, vlm, or embeddings")
   (load-state model-state-p "Whether model is loaded")
   (publisher stringp "Model publisher" :default "")
   (arch stringp "Model architecture" :default "")
   (quantization stringp "Quantization level" :default "")
   (max-context-length natp "Maximum context length" :default 0)
   (loaded-context-length natp "Loaded context length (0 if not loaded)" :default 0))
  :layout :list)

;; Predicate helpers
(define model-loaded-p ((m model-info-p))
  :returns (loaded booleanp)
  (let ((st (model-info->load-state m)))
    (model-state-case st
      :loaded t
      :not-loaded nil)))

(define model-is-llm-p ((m model-info-p))
  :returns (is-llm booleanp)
  (let ((tp (model-info->type m)))
    (model-type-case tp
      :llm t
      :otherwise nil)))

(define model-is-completions-p ((m model-info-p))
  :returns (is-completions booleanp)
  "True for models that can do chat/text completions (llm or vlm)"
  (let ((tp (model-info->type m)))
    (model-type-case tp
      :llm t
      :vlm t
      :embeddings nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Model Info List
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist model-info-list
  :elt-type model-info-p
  :true-listp t)

;; Filter helpers - use simpler approach without return type proofs
;; (ACL2 has trouble with recursive filter return types on FTY lists)
(defun filter-loaded-models (models)
  (declare (xargs :guard (model-info-list-p models)))
  (cond ((endp models) nil)
        ((model-loaded-p (model-info-fix (car models)))
         (cons (model-info-fix (car models)) 
               (filter-loaded-models (cdr models))))
        (t (filter-loaded-models (cdr models)))))

(defun filter-completions-models (models)
  (declare (xargs :guard (model-info-list-p models)))
  (cond ((endp models) nil)
        ((model-is-completions-p (model-info-fix (car models)))
         (cons (model-info-fix (car models)) 
               (filter-completions-models (cdr models))))
        (t (filter-completions-models (cdr models)))))

(defun filter-loaded-completions-models (models)
  (declare (xargs :guard (model-info-list-p models)))
  (filter-loaded-models (filter-completions-models models)))

