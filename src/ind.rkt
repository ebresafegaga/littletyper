#lang pie

(claim a Trivial)
(define a sole)

(claim Maybe (-> U U))
(define Maybe (λ (X) (Either X Trivial)))

(claim nothing (Π ((E U)) (Maybe E)))
(define nothing (λ (E) (right sole)))

(claim just (Π ((E U)) (-> E (Maybe E))))
(define just (λ (E e) (left e)))

(claim maybe-head (Π ((E U)) (-> (List E) (Maybe E))))
(define maybe-head (λ (E es) (rec-List es (nothing E) (λ (hd tl hd-rest) (just E hd)))))


(claim maybe-tail
  (Π ((E U))
    (-> (List E)
        (Maybe (List E)))))
(define maybe-tail
  (λ (E es)
    (rec-List es
      (nothing (List E))
      (λ (hd tl tl-rest) (just (List E) tl)))))

(claim list-ref
  (Π ((E U))
    (-> Nat (List E)
        (Maybe E))))
(define list-ref
  (λ (E n)
    (rec-Nat n
      (maybe-head E)
      (λ (k f)
        (λ (es)
          (ind-Either (maybe-tail E es)
            (λ (maybe) (Maybe E))
            (λ (tl) (f tl))
            (λ (empty) (nothing E))))))))



(claim Fin
  (-> Nat
      U))
(define Fin
  (λ (n)
    (iter-Nat n
      Absurd
      Maybe)))


(claim fzero
  (Π ((n Nat))
    (Fin (add1 n))))
(define fzero
  (λ (n)
    (nothing (Fin n))))


(claim fadd1
  (Π ((n Nat))
    (-> (Fin n)
        (Fin (add n)))))
(define fadd1
  (λ (n fin-n)
    (just (Fin n) n)))

(claim base-vec-ref
  (Π ((E U))
    (-> (Fin zero) (Vec E zero)
        E)))
(define base-vec-ref
  (λ (E)
    (λ (no-value-ever es)
      (ind-Absurd no-value-ever
        E))))

(claim step-vec-ref
  (Π ((E U)
      (l Nat))
    (-> (-> (Fin l) (Vec E l) E)
        (-> (Fin (add1 l)) (Vec E (add1 l)) E))))
(define step-vec-ref
  (λ (E l)
    (λ (f)
      (λ (fin es)
        (ind-Either fin
          (λ (i) E)
          (λ (fin-rest) (f fin-rest (tail es)))
          (λ (triv) (head es)))))))

(claim vec-ref
  (Π ((E U)
      (l Nat))
    (-> (Fin l) (Vec E l)
        E)))
(define vec-ref
  (λ (E l)
    (ind-Nat l
      (λ (k) (-> (Fin k) (Vec E k) E))
      (base-vec-ref E)
      (step-vec-ref E))))







 





 
