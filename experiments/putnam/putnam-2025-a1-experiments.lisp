(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PUTNAM 2025 A1 - EXPERIMENTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; This file contains work in progress on proving diff-eventually-power-of-2.
;;; Once complete, the proven theorems should be moved to putnam-2025-a1-solution.lisp.
;;;
;;; Goal: Prove that for k >= odd-part(|m0-n0|), the difference |m_k - n_k|
;;; is a power of 2.
;;;
;;; Key insight: |m' - n'| = 2|m-n|/g where g = gcd(2m+1, 2n+1).
;;; - When g > 1 (odd), odd-part decreases: odd-part(|m'-n'|) = odd-part(|m-n|)/g
;;; - When g = 1, odd-part preserved: odd-part(2|m-n|) = odd-part(|m-n|)
;;;
;;; After at most odd-part(|m0-n0|) steps with g > 1, odd-part becomes 1.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Include the solution file which has all the base machinery
(include-book "putnam-2025-a1-solution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ODD-PART LEMMAS NEEDED
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; odd-part(2n) = odd-part(n) - multiplying by 2 doesn't change odd-part
(defthm odd-part-times-2
  (implies (posp n)
           (equal (odd-part (* 2 n)) (odd-part n)))
  :hints (("Goal" :expand ((odd-part (* 2 n))))))

;; odd-part is always odd
(defthm odd-part-oddp
  (implies (posp n)
           (oddp (odd-part n)))
  :hints (("Goal" :in-theory (enable oddp evenp))))

;; odd-part divides n  
(defthm odd-part-divides
  (implies (posp n)
           (integerp (/ n (odd-part n))))
  :hints (("Goal" :in-theory (enable evenp))))

;; KEY LEMMA NEEDED:
;; When we divide by an odd number g, odd-part(n/g) = odd-part(n)/g
;; This requires showing that dividing by an odd number doesn't affect
;; the power-of-2 factor in n.
;;
;; Proof sketch:
;; - n = odd-part(n) * 2^k for some k
;; - If g is odd and divides n, then g must divide odd-part(n) 
;;   (since gcd(g, 2^k) = 1)
;; - So n/g = (odd-part(n)/g) * 2^k
;; - Therefore odd-part(n/g) = odd-part(n)/g

;; TODO: Prove odd-part-div-by-odd
;; (defthm odd-part-div-by-odd
;;   (implies (and (posp n) (posp g) (oddp g) (integerp (/ n g)))
;;            (equal (odd-part (/ n g))
;;                   (/ (odd-part n) g))))

