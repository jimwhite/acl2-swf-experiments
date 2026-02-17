(in-package "ACL2")

;;;; =========================================================================
;;;; Forest Friends Frenzy — Formally Verified Logic Puzzle
;;;; =========================================================================
;;;;
;;;; A logic puzzle set in the Hundred Acre Wood, verified in ACL2.
;;;;
;;;; PLAYERS: Winnie the Pooh, Piglet, Tigger, Eeyore
;;;; ACTIVITIES: honey tasting, bouncing, exploring, gardening
;;;; TIMES: morning, noon, afternoon, evening
;;;;
;;;; ENCODING (integers 1–4):
;;;;   Friends:    1=Pooh, 2=Piglet, 3=Tigger, 4=Eeyore
;;;;   Activities: 1=honey-tasting, 2=bouncing, 3=exploring, 4=gardening
;;;;   Times:      1=morning, 2=noon, 3=afternoon, 4=evening
;;;;
;;;; ── Part I: Original Puzzle (BUGGY — 27 solutions) ──────────────────────
;;;; ── Part II: Fixed Puzzle (VERIFIED — unique solution) ──────────────────
;;;; ── Part III: Proven properties ─────────────────────────────────────────

;;;; =========================================================================
;;;; Utility Definitions
;;;; =========================================================================

;; A valid slot is an integer in {1, 2, 3, 4}
(defun slot-p (x)
  (and (integerp x) (<= 1 x) (<= x 4)))

;; All four values are pairwise distinct
(defun all-diff-4 (a b c d)
  (and (not (equal a b)) (not (equal a c)) (not (equal a d))
       (not (equal b c)) (not (equal b d))
       (not (equal c d))))

;;;; =========================================================================
;;;; Part I: Original (Buggy) Puzzle
;;;; =========================================================================
;;;;
;;;; Original Clues:
;;;;   1. Tigger does his activity earlier than Eeyore.
;;;;   2. Honey tasting happens later than exploring.
;;;;   3. Piglet performs his activity in the morning.
;;;;   4. Pooh does not like gardening.
;;;;
;;;; These 4 clues admit 27 valid solutions (verified by Python constraint
;;;; solver). The published walkthrough contains a logical error in Step 3:
;;;;
;;;;   FLAWED REASONING: "since Piglet occupies morning, Tigger must do
;;;;   his activity at noon, and Eeyore does his in the afternoon"
;;;;
;;;;   TRUTH: Tigger < Eeyore leaves THREE possible arrangements for
;;;;   {Tigger, Pooh, Eeyore} over {noon, afternoon, evening}:
;;;;     (a) Tigger=noon, Eeyore=afternoon, Pooh=evening
;;;;     (b) Tigger=noon, Eeyore=evening,   Pooh=afternoon  ← intended
;;;;     (c) Tigger=afternoon, Eeyore=evening, Pooh=noon

(defun puzzle-original (aP aI aT aE tP tI tT tE)
  (and
   ;; Domain: all values are slots 1..4
   (slot-p aP) (slot-p aI) (slot-p aT) (slot-p aE)
   (slot-p tP) (slot-p tI) (slot-p tT) (slot-p tE)
   ;; Each friend has a different activity
   (all-diff-4 aP aI aT aE)
   ;; Each friend has a different time
   (all-diff-4 tP tI tT tE)
   ;; Clue 1: Tigger < Eeyore
   (< tT tE)
   ;; Clue 2: honey-tasting(1) later than exploring(3)
   (implies (equal aP 1) (and (implies (equal aI 3) (> tP tI))
                              (implies (equal aT 3) (> tP tT))
                              (implies (equal aE 3) (> tP tE))))
   (implies (equal aI 1) (and (implies (equal aP 3) (> tI tP))
                              (implies (equal aT 3) (> tI tT))
                              (implies (equal aE 3) (> tI tE))))
   (implies (equal aT 1) (and (implies (equal aP 3) (> tT tP))
                              (implies (equal aI 3) (> tT tI))
                              (implies (equal aE 3) (> tT tE))))
   (implies (equal aE 1) (and (implies (equal aP 3) (> tE tP))
                              (implies (equal aI 3) (> tE tI))
                              (implies (equal aT 3) (> tE tT))))
   ;; Clue 3: Piglet = morning
   (equal tI 1)
   ;; Clue 4: Pooh ≠ gardening(4)
   (not (equal aP 4))))

;;;; ── Part I Theorems ──────────────────────────────────────────────────────

;; The proposed solution IS valid under the original clues
(defthm original-proposed-solution-valid
  (puzzle-original 2 4 3 1  ; Pooh=bouncing, Piglet=gardening, Tigger=exploring, Eeyore=honey
                   3 1 2 4) ; Pooh=afternoon, Piglet=morning, Tigger=noon, Eeyore=evening
  :rule-classes nil)

;; An ALTERNATIVE solution also satisfies the original clues (non-uniqueness!)
(defthm original-has-alternative-solution
  (puzzle-original 3 4 2 1  ; Pooh=exploring, Piglet=gardening, Tigger=bouncing, Eeyore=honey
                   3 1 2 4) ; Pooh=afternoon, Piglet=morning, Tigger=noon, Eeyore=evening
  :rule-classes nil)

;; The two solutions are genuinely different
(defthm original-solutions-differ
  (not (equal (list 2 4 3 1 3 1 2 4)    ; proposed
              (list 3 4 2 1 3 1 2 4)))   ; alternative
  :rule-classes nil)

;; A third solution with DIFFERENT time assignments also works
(defthm original-has-third-distinct-solution
  (puzzle-original 3 4 2 1  ; Pooh=exploring, Piglet=gardening, Tigger=bouncing, Eeyore=honey
                   2 1 3 4) ; Pooh=noon, Piglet=morning, Tigger=afternoon, Eeyore=evening
  :rule-classes nil)

;; The description's claim "Tigger=noon, Eeyore=afternoon" is NOT provable
;; (ACL2 correctly rejects this — tested interactively, proof fails with NIL subgoal)

;; What IS provable from the original clues:

;; Piglet is always morning (direct from Clue 3)
(defthm original-piglet-always-morning
  (implies (puzzle-original aP aI aT aE tP tI tT tE)
           (equal tI 1))
  :rule-classes nil)

;; Tigger always goes before Eeyore (direct from Clue 1)
(defthm original-tigger-before-eeyore
  (implies (puzzle-original aP aI aT aE tP tI tT tE)
           (< tT tE))
  :rule-classes nil)

;; Pooh never does gardening (direct from Clue 4)
(defthm original-pooh-never-gardens
  (implies (puzzle-original aP aI aT aE tP tI tT tE)
           (not (equal aP 4)))
  :rule-classes nil)


;;;; =========================================================================
;;;; Part II: Fixed Puzzle — UNIQUE SOLUTION
;;;; =========================================================================
;;;;
;;;; To make the puzzle uniquely solvable while keeping the same intended
;;;; solution, we add two thematic clues and strengthen one:
;;;;
;;;;   1. Piglet performs his activity in the morning.         [unchanged]
;;;;   2. Tigger does his activity earlier than Eeyore.        [unchanged]
;;;;   3. Pooh does not like gardening OR honey tasting.       [strengthened]
;;;;   4. Honey tasting happens later than exploring.          [unchanged]
;;;;   5. Tigger's favorite activity is exploring.             [NEW]
;;;;   6. Pooh does his activity later than Tigger but         [NEW]
;;;;      earlier than Eeyore.
;;;;
;;;; Thematic justification:
;;;;   Clue 3: Pooh is known for honey but "tasting" is too refined for him;
;;;;           he just eats it. He's also not a gardener.
;;;;   Clue 5: Tigger's personality — "the wonderful thing about Tiggers"
;;;;           is that he explores everywhere.
;;;;   Clue 6: Pooh takes his time but isn't as slow as Eeyore.

(defun puzzle-fixed (aP aI aT aE tP tI tT tE)
  (and
   ;; Domain
   (slot-p aP) (slot-p aI) (slot-p aT) (slot-p aE)
   (slot-p tP) (slot-p tI) (slot-p tT) (slot-p tE)
   ;; All-different
   (all-diff-4 aP aI aT aE)
   (all-diff-4 tP tI tT tE)
   ;; Clue 1: Piglet = morning(1)
   (equal tI 1)
   ;; Clue 2: Tigger < Eeyore
   (< tT tE)
   ;; Clue 3 (strengthened): Pooh ≠ gardening(4) AND Pooh ≠ honey-tasting(1)
   (not (equal aP 4))
   (not (equal aP 1))
   ;; Clue 4: honey-tasting(1) later than exploring(3)
   ;; Since Tigger=exploring (Clue 5), this simplifies to:
   ;; whoever does honey tasting has a later time than Tigger.
   (implies (equal aP 1) (> tP tT))
   (implies (equal aI 1) (> tI tT))
   (implies (equal aE 1) (> tE tT))
   ;; (Tigger can't have honey since aT=3 from Clue 5)
   ;; Clue 5: Tigger = exploring(3)
   (equal aT 3)
   ;; Clue 6: Tigger < Pooh < Eeyore
   (< tT tP)
   (< tP tE)))

;;;; ── Part II Theorems ─────────────────────────────────────────────────────

;; EXISTENCE: The fixed puzzle has at least one solution
(defthm fixed-puzzle-satisfiable
  (puzzle-fixed 2 4 3 1   ; Pooh=bouncing, Piglet=gardening, Tigger=exploring, Eeyore=honey
                3 1 2 4)  ; Pooh=afternoon, Piglet=morning, Tigger=noon, Eeyore=evening
  :rule-classes nil)

;; UNIQUENESS: The fixed puzzle has EXACTLY one solution
;; ACL2 proves this by exhaustive case analysis over the finite domain.
(defthm fixed-puzzle-unique-solution
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (and (equal aP 2)   ; Pooh = bouncing
                (equal aI 4)   ; Piglet = gardening
                (equal aT 3)   ; Tigger = exploring
                (equal aE 1)   ; Eeyore = honey tasting
                (equal tP 3)   ; Pooh = afternoon
                (equal tI 1)   ; Piglet = morning
                (equal tT 2)   ; Tigger = noon
                (equal tE 4))) ; Eeyore = evening
  :rule-classes nil)


;;;; =========================================================================
;;;; Part III: Deduction Chain Properties
;;;; =========================================================================
;;;;
;;;; These theorems verify the CORRECT step-by-step deduction process
;;;; that a player should follow to solve the fixed puzzle.

;; Step 1: Piglet is in the morning (direct from Clue 1)
(defthm step-1-piglet-morning
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (equal tI 1))
  :rule-classes nil)

;; Step 2: The time ordering is completely determined:
;;         Tigger=noon, Pooh=afternoon, Eeyore=evening
(defthm step-2-time-ordering
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (and (equal tT 2) (equal tP 3) (equal tE 4)))
  :rule-classes nil)

;; Step 3: Tigger's activity is exploring (direct from Clue 5)
(defthm step-3-tigger-explores
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (equal aT 3))
  :rule-classes nil)

;; Step 4: Eeyore does honey tasting
;; (He's the only one who can: Pooh can't (Clue 3), Tigger explores (Clue 5),
;;  and honey tasting must be after exploring, i.e., after Tigger=noon.
;;  Eeyore at evening satisfies this; Piglet at morning does not.)
(defthm step-4-eeyore-honey
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (equal aE 1))
  :rule-classes nil)

;; Step 5: Pooh bounces (only remaining non-gardening activity)
(defthm step-5-pooh-bounces
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (equal aP 2))
  :rule-classes nil)

;; Step 6: Piglet gardens (last activity remaining)
(defthm step-6-piglet-gardens
  (implies (puzzle-fixed aP aI aT aE tP tI tT tE)
           (equal aI 4))
  :rule-classes nil)

;;;; =========================================================================
;;;; Part IV: Redundancy Analysis
;;;; =========================================================================
;;;;
;;;; Which clues are actually needed? We show Clue 2 is subsumed by Clue 6.

;; Clue 2 (Tigger < Eeyore) is redundant given Clue 6 (Tigger < Pooh < Eeyore)
(defthm clue-2-redundant
  (implies (and (< tT tP) (< tP tE))
           (< tT tE))
  :rule-classes nil)

;;;; =========================================================================
;;;; Solution Grid (for the fixed puzzle)
;;;; =========================================================================
;;;;
;;;;   Friend          Activity        Time of Day
;;;;   ──────────────  ──────────────  ───────────
;;;;   Winnie the Pooh Bouncing        Afternoon
;;;;   Piglet          Gardening       Morning
;;;;   Tigger          Exploring       Noon
;;;;   Eeyore          Honey Tasting   Evening
;;;;
;;;; =========================================================================
