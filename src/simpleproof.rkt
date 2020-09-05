#lang pie


(claim A U)
(define A
  (-> (= Nat 5 6) Absurd))

(claim =consequence
  (-> Nat Nat
      U))
(define =consequence
  (λ (a b)
    (which-Nat a
      (which-Nat b
        Trivial
        (λ (b-1) Absurd))
      (λ (a-1)
        (which-Nat b
          Absurd
          (λ (b-1) (= Nat a-1 b-1)))))))

(claim =consequence-same
  (Π ((n Nat))
    (=consequence n n)))
(define =consequence-same
  (λ (n)
    (ind-Nat n
      (λ (k) (=consequnce k k))
      sole
      (λ (n rest) (same n)))))

(claim mot-front
  (Π ((E U)
      (k Nat))
    (-> (Vec E k)
        U)))
(define mot-front
  (λ (E)
    (λ (k es)
      (Π ((j Nat)) 
        (-> (= Nat k (add1 j))
            E)))))

(claim step-front
  (Π ((E U)
      (l Nat)
      (e E)
      (es (Vec E l)))
    (-> (mot-front E l es)
        (mot-front E (add1 l) (vec:: e es)))))
(define step-front
  (λ (E l e es)
    (λ (front-es)
      (λ (j proof) e))))



(claim front
  (Π ((E U)
      (n Nat))
    (-> (Vec E (add1 n))
        E)))
(define front
  (λ (E n es)
    (ind-Vec (add1 n) es
      (λ (k xs) E)
      (TODO)
      (λ (k h t front-r) h))))




