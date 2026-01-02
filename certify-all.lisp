(in-package "ACL2")

;; certify-all.lisp
;;
;; Top-level book that includes all experiments.
;; Certifying this book verifies that all proofs in the repository work.
;;
;; Usage:
;;   cert.pl certify-all.lisp
;;
;; This is the ACL2 idiomatic way to create a "build script" - a single
;; book that depends on everything else. If certification succeeds, all
;; theorems are verified.

;; Arithmetic experiments
(include-book "experiments/arithmetic/experiment-01-hello-world")
(include-book "experiments/arithmetic/experiment-02-induction-basics")
(include-book "experiments/arithmetic/experiment-03-basics")
(include-book "experiments/arithmetic/experiment-04-natural-numbers")
(include-book "experiments/arithmetic/experiment-04-natural-numbers-correctness")

;; List experiments
(include-book "experiments/lists/experiment-01-list-basics")
(include-book "experiments/lists/experiment-02-higher-order")
(include-book "experiments/lists/experiment-02-higher-order-product")

;; Challenge problems
;; Note: challenge-problems.lisp is work-in-progress and not yet certifiable
;; (include-book "experiments/challenge-problems")
(include-book "experiments/trivial-swf-exercises")

;; Success marker
(defthm all-experiments-certified
  ;; This trivial theorem will only be admitted if all includes succeeded
  (equal t t)
  :rule-classes nil)
