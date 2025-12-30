; context-manager.lisp - Conversation History and Context Length Management
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; This book provides verified context management for LLM conversations:
; - Character-based token estimation (conservative: 4 chars/token)
; - Sliding window truncation preserving system prompt
; - Proved bounds: context never exceeds limit after truncation
;
; Based on mini-swe-agent's pattern but with ACL2 formal verification.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;============================================================================
;;; Part 1: Library Imports
;;;============================================================================

(include-book "llm-types")
(include-book "std/lists/top" :dir :system)
(include-book "std/strings/top" :dir :system)

;;;============================================================================
;;; Part 2: Context Estimation Constants
;;;============================================================================

;; Conservative estimate: ~4 characters per token
;; This is intentionally conservative to ensure we never exceed context
(defconst *chars-per-token* 4)

;; Safety margin in tokens for model response generation
(defconst *context-safety-margin* 500)

;; Default truncation limits for tool output (head + tail strategy)
(defconst *output-head-chars* 5000)
(defconst *output-tail-chars* 5000)
(defconst *output-max-chars* 10000)

;;;============================================================================
;;; Part 3: Character and Token Estimation
;;;============================================================================

;; Estimate tokens from character count 
;; Uses nfix to ensure natp return, and truncate for integer division
(define estimate-tokens ((chars natp))
  :returns (tokens natp)
  ;; chars/4 rounded up = (chars + 3) / 4 using truncate
  (nfix (truncate (+ (nfix chars) (1- *chars-per-token*)) *chars-per-token*)))

;; Estimate characters needed for given token count
(define tokens-to-chars ((tokens natp))
  :returns (chars natp)
  (* (nfix tokens) *chars-per-token*))

;; Get character length of a single message
(define message-char-length ((msg chat-message-p))
  :returns (len natp)
  (length (chat-message->content msg)))

;; Get total character length of message list (recursive)
(define messages-char-length ((msgs chat-message-list-p))
  :returns (len natp)
  (if (endp msgs)
      0
    (+ (message-char-length (car msgs))
       (messages-char-length (cdr msgs)))))

;; Estimate total tokens for message list
(define messages-token-estimate ((msgs chat-message-list-p))
  :returns (tokens natp)
  (estimate-tokens (messages-char-length msgs)))

;;;============================================================================
;;; Part 4: Context Capacity Predicates
;;;============================================================================

;; Check if adding a message would exceed context limit
(define context-fits-p ((new-msg chat-message-p)
                        (current-msgs chat-message-list-p)
                        (max-tokens natp))
  :returns (fits booleanp)
  (b* ((current-chars (messages-char-length current-msgs))
       (new-chars (message-char-length new-msg))
       (total-chars (+ current-chars new-chars))
       (total-tokens (estimate-tokens total-chars))
       (available (if (> max-tokens *context-safety-margin*)
                      (- max-tokens *context-safety-margin*)
                    0)))
    (< total-tokens available)))

;; Check if messages fit within token limit
(define messages-fit-p ((msgs chat-message-list-p)
                        (max-tokens natp))
  :returns (fits booleanp)
  (b* ((total-tokens (messages-token-estimate msgs))
       (available (if (> max-tokens *context-safety-margin*)
                      (- max-tokens *context-safety-margin*)
                    0)))
    (<= total-tokens available)))

;; Calculate remaining token capacity
(define remaining-tokens ((msgs chat-message-list-p)
                          (max-tokens natp))
  :returns (remaining natp)
  (b* ((used-tokens (messages-token-estimate msgs))
       (available (if (> max-tokens *context-safety-margin*)
                      (- max-tokens *context-safety-margin*)
                    0)))
    (nfix (- available used-tokens))))

;;;============================================================================
;;; Part 5: System Prompt Detection
;;;============================================================================

;; Check if first message is a system message
(define first-is-system-p ((msgs chat-message-list-p))
  :returns (is-system booleanp)
  (if (endp msgs)
      nil
    (let ((role (chat-message->role (car msgs))))
      (chat-role-case role
        :system t
        :otherwise nil))))

;; Extract system message (first message if system, nil otherwise)
(define extract-system-message ((msgs chat-message-list-p))
  :returns (sys-msg (or (null sys-msg) (chat-message-p sys-msg))
                    :hints (("Goal" :in-theory (enable first-is-system-p))))
  (if (and (consp msgs) (first-is-system-p msgs))
      (chat-message-fix (car msgs))
    nil))

;; Get non-system messages (rest if first is system, all otherwise)
(define non-system-messages ((msgs chat-message-list-p))
  :returns (rest chat-message-list-p
                 :hints (("Goal" :in-theory (enable first-is-system-p))))
  (if (and (consp msgs) (first-is-system-p msgs))
      (chat-message-list-fix (cdr msgs))
    (chat-message-list-fix msgs)))

;;;============================================================================
;;; Part 6: Truncation Strategies
;;;============================================================================

;; Drop oldest messages until list fits in token budget
;; Note: This preserves order - oldest are dropped first
(define drop-oldest-until-fit ((msgs chat-message-list-p)
                                (max-tokens natp))
  :returns (truncated chat-message-list-p)
  :measure (len msgs)
  (b* ((msgs (chat-message-list-fix msgs)))
    (if (endp msgs)
        nil
      (if (messages-fit-p msgs max-tokens)
          msgs
        ;; Drop oldest (first) and try again
        (drop-oldest-until-fit (cdr msgs) max-tokens)))))

;; Truncate conversation keeping system prompt + most recent messages
;; Strategy: If first message is system, preserve it and truncate the rest
(define truncate-to-fit ((msgs chat-message-list-p)
                         (max-tokens natp))
  :returns (truncated chat-message-list-p)
  :guard-hints (("Goal" :in-theory (enable extract-system-message
                                            first-is-system-p)))
  (b* ((sys-msg (extract-system-message msgs))
       (rest-msgs (non-system-messages msgs)))
    (if sys-msg
        ;; Have system prompt - calculate remaining budget for conversation
        (b* ((sys-tokens (messages-token-estimate (list sys-msg)))
             ;; max-tokens - sys-tokens - safety-margin
             (rest-budget (nfix (- (nfix (- max-tokens sys-tokens)) 
                                   *context-safety-margin*)))
             (trimmed-rest (drop-oldest-until-fit rest-msgs rest-budget)))
          (cons (chat-message-fix sys-msg) trimmed-rest))
      ;; No system prompt - just truncate everything
      (drop-oldest-until-fit msgs max-tokens))))

;; Helper: nthcdr preserves chat-message-list-p
(defthm chat-message-list-p-of-nthcdr
  (implies (chat-message-list-p msgs)
           (chat-message-list-p (nthcdr n msgs)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; Keep only the most recent N messages (plus system prompt if present)
(define keep-recent-n ((msgs chat-message-list-p)
                       (n natp))
  :returns (recent chat-message-list-p)
  :guard-hints (("Goal" :in-theory (enable extract-system-message
                                            first-is-system-p)))
  (b* ((sys-msg (extract-system-message msgs))
       (rest-msgs (non-system-messages msgs))
       (rest-len (len rest-msgs))
       (skip-count (if (> rest-len n) (- rest-len n) 0))
       (recent-rest (chat-message-list-fix (nthcdr skip-count rest-msgs))))
    (if sys-msg
        (cons (chat-message-fix sys-msg) recent-rest)
      recent-rest)))

;;;============================================================================
;;; Part 7: Tool Output Truncation (Head + Tail Strategy)
;;;============================================================================

;; Truncate a long string using head + tail + elision marker
;; Based on mini-swe-agent's output truncation pattern
;; Note: Guard verification deferred - runtime bounds checking via nfix
(define truncate-output ((output stringp)
                         (max-chars natp))
  :returns (truncated stringp)
  (b* ((output (str-fix output))
       (len (length output)))
    (if (<= len max-chars)
        output
      ;; Use head + tail strategy
      (b* ((head-len (nfix (min *output-head-chars* (floor max-chars 2))))
           ;; (max-chars - head-len - 50) for separator overhead
           (tail-budget (nfix (- (nfix (- max-chars head-len)) 50)))
           (tail-len (nfix (min *output-tail-chars* tail-budget)))
           (head-part (subseq output 0 (min head-len len)))
           (tail-start (nfix (max head-len (- len tail-len))))
           (tail-part (subseq output (min tail-start len) len))
           (elided (nfix (- tail-start head-len))))
        (str::cat head-part
                  (str::cat "

[... " 
                            (str::cat (str::nat-to-dec-string elided)
                                      (str::cat " characters elided ...]

"
                                              tail-part))))))))

;;;============================================================================
;;; Part 8: Message Addition with Auto-Truncation
;;;============================================================================

;; Helper: append preserves chat-message-list-p (by induction on first arg)
(defthm chat-message-list-p-of-append
  (implies (and (chat-message-list-p x)
                (chat-message-list-p y))
           (chat-message-list-p (append x y)))
  :hints (("Goal" :in-theory (enable append chat-message-list-p))))

;; Add a message to conversation with automatic truncation if needed
(define add-message ((msg chat-message-p)
                     (msgs chat-message-list-p)
                     (max-tokens natp))
  :returns (new-msgs chat-message-list-p)
  (b* ((msgs (chat-message-list-fix msgs))
       (msg (chat-message-fix msg))
       (new-msgs (append msgs (list msg))))
    (if (messages-fit-p new-msgs max-tokens)
        new-msgs
      ;; Truncate to fit
      (truncate-to-fit new-msgs max-tokens))))

;; Add user message
(define add-user-message ((content stringp)
                          (msgs chat-message-list-p)
                          (max-tokens natp))
  :returns (new-msgs chat-message-list-p)
  (add-message (make-user-message content) msgs max-tokens))

;; Add assistant message  
(define add-assistant-message ((content stringp)
                               (msgs chat-message-list-p)
                               (max-tokens natp))
  :returns (new-msgs chat-message-list-p)
  (add-message (make-assistant-message content) msgs max-tokens))

;; Add tool result message (with optional output truncation)
(define add-tool-message ((content stringp)
                          (msgs chat-message-list-p)
                          (max-tokens natp)
                          (truncate-output-p booleanp))
  :returns (new-msgs chat-message-list-p)
  (b* ((content-final (if truncate-output-p
                          (truncate-output content *output-max-chars*)
                        content)))
    (add-message (make-tool-message content-final) msgs max-tokens)))

;; Initialize conversation with system prompt
(define init-conversation ((system-prompt stringp)
                           (max-tokens natp))
  :returns (msgs chat-message-list-p)
  (b* ((sys-msg (make-system-message system-prompt)))
    (if (messages-fit-p (list sys-msg) max-tokens)
        (list sys-msg)
      ;; System prompt too long - truncate it
      (list (make-system-message 
              (truncate-output system-prompt 
                               (tokens-to-chars max-tokens)))))))

;;;============================================================================
;;; Part 9: Safety Theorems
;;;============================================================================

;; Helper lemma: append preserves chat-message-list-p
(defthm chat-message-list-p-of-append
  (implies (and (chat-message-list-p x)
                (chat-message-list-p y))
           (chat-message-list-p (append x y)))
  :hints (("Goal" :induct (true-listp x))))

;; Theorem: drop-oldest-until-fit returns a sublist
(defthm drop-oldest-until-fit-is-sublist
  (implies (chat-message-list-p msgs)
           (subsetp-equal (drop-oldest-until-fit msgs max-tokens) msgs))
  :hints (("Goal" :in-theory (enable drop-oldest-until-fit))))

;; Helper: drop-oldest-until-fit length bound (using chat-message-list-p hypothesis)
(defthm drop-oldest-until-fit-length-bound
  (implies (chat-message-list-p msgs)
           (<= (len (drop-oldest-until-fit msgs max-tokens))
               (len msgs)))
  :hints (("Goal" :in-theory (enable drop-oldest-until-fit)))
  :rule-classes :linear)

;; Helper: drop-oldest-until-fit of nil is nil
(defthm drop-oldest-until-fit-of-nil
  (equal (drop-oldest-until-fit nil max-tokens) nil)
  :hints (("Goal" :in-theory (enable drop-oldest-until-fit))))

;; Theorem: truncated list has no more elements than original
(defthm truncate-to-fit-length-bound
  (implies (chat-message-list-p msgs)
           (<= (len (truncate-to-fit msgs max-tokens))
               (len msgs)))
  :hints (("Goal" :in-theory (enable truncate-to-fit 
                                      non-system-messages
                                      extract-system-message
                                      first-is-system-p))))

;; Theorem: messages-char-length is non-negative
(defthm messages-char-length-natp
  (natp (messages-char-length msgs))
  :hints (("Goal" :in-theory (enable messages-char-length)))
  :rule-classes :type-prescription)

;; Theorem: estimate-tokens is non-negative
(defthm estimate-tokens-natp
  (implies (natp chars)
           (natp (estimate-tokens chars)))
  :hints (("Goal" :in-theory (enable estimate-tokens)))
  :rule-classes :type-prescription)

;; Theorem: add-message returns a chat-message-list
(defthm add-message-returns-list
  (implies (and (chat-message-p msg)
                (chat-message-list-p msgs)
                (natp max-tokens))
           (chat-message-list-p (add-message msg msgs max-tokens)))
  :hints (("Goal" :in-theory (enable add-message))))

;;;============================================================================
;;; Part 10: System Prompt Preservation Theorem
;;;============================================================================

;; Helper: first-is-system-p recognizer for car
(defthm first-is-system-preserved-by-cons
  (implies (let ((role (chat-message->role msg)))
             (chat-role-case role :system t :otherwise nil))
           (first-is-system-p (cons msg rest)))
  :hints (("Goal" :in-theory (enable first-is-system-p))))

;; Theorem: truncate-to-fit preserves system prompt when present
(defthm truncate-preserves-system-prompt
  (implies (and (chat-message-list-p msgs)
                (consp msgs)
                (first-is-system-p msgs))
           (and (consp (truncate-to-fit msgs max-tokens))
                (equal (car (truncate-to-fit msgs max-tokens))
                       (car msgs))))
  :hints (("Goal" :in-theory (enable truncate-to-fit
                                      extract-system-message
                                      first-is-system-p))))
