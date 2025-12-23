; Basic list theorems inspired by Software Foundations
; Source: https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html
;
; These theorems parallel the Coq proofs in the Lists chapter,
; adapted for ACL2's list operations.
;
; All theorems now prove successfully using helper lemmas about revappend
; and careful theory control to avoid rewrite loops.

(in-package "ACL2")

; Theorem nil_app: ∀ l, [] ++ l = l
; Source: Software Foundations Lists.v, nil_app
; In ACL2: (append nil l) = l
(defthm nil-app
  (implies (true-listp l)
           (equal (append nil l) l)))

; Theorem app_assoc: ∀ l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
; Source: Software Foundations Lists.v, app_assoc
(defthm app-assoc
  (implies (and (true-listp l1)
                (true-listp l2)
                (true-listp l3))
           (equal (append (append l1 l2) l3)
                  (append l1 (append l2 l3)))))

; Helper lemma: length of revappend
; ACL2's reverse is defined using revappend, so we need this helper
(local
 (defthm len-revappend
   (implies (true-listp acc)
            (equal (len (revappend x acc))
                   (+ (len x) (len acc))))))

; Theorem rev_length: ∀ l, length(rev(l)) = length(l)
; Source: Software Foundations Lists.v, rev_length (exercise)
(defthm rev-length
  (implies (true-listp l)
           (equal (len (reverse l))
                  (len l))))

; Helper lemmas for reverse/revappend theorems
; These must be proved in order to avoid rewrite loops

; Step 1: Basic property of revappend with append
(local
 (defthm append-revappend
   (equal (append (revappend x y) z)
          (revappend x (append y z)))))

; Step 2: Fundamental characterization of revappend
; This shows how revappend relates to reverse and append
(local
 (defthm revappend-is-append-reverse
   (equal (revappend x y)
          (append (reverse x) y))))

; Step 3: How revappend interacts with append
; Must disable revappend-is-append-reverse to prevent rewrite loops
(local
 (defthm revappend-of-append-lists
   (equal (revappend (append x y) acc)
          (revappend y (revappend x acc)))
   :hints (("Goal" :in-theory (disable revappend-is-append-reverse)))))

; Theorem rev_app_distr: ∀ l1 l2, rev(l1 ++ l2) = rev(l2) ++ rev(l1)
; Source: Software Foundations Lists.v, rev_app_distr
; Now proves automatically using the helper lemmas above
(defthm rev-app-distr
  (implies (and (true-listp l1)
                (true-listp l2))
           (equal (reverse (append l1 l2))
                  (append (reverse l2) (reverse l1)))))

; Helper lemma for rev-involutive: double revappend
; From ACL2 documentation: revappend-revappend theorem
; Need to disable lemmas that might cause loops
(local
 (defthm revappend-revappend
   (equal (revappend (revappend x y) z)
          (revappend y (append x z)))
   :hints (("Goal" :in-theory (disable revappend-is-append-reverse
                                        revappend-of-append-lists)))))

; Theorem rev_involutive: ∀ l, rev(rev(l)) = l
; Source: Software Foundations Lists.v, rev_involutive
; Must disable revappend-is-append-reverse to avoid rewrite loops
(defthm rev-involutive
  (implies (true-listp l)
           (equal (reverse (reverse l)) l))
  :hints (("Goal" :in-theory (disable revappend-is-append-reverse))))

; Additional theorem: append with nil on right
; This is implicit in Software Foundations but useful in ACL2
(defthm app-nil-r
  (implies (true-listp l)
           (equal (append l nil) l)))
