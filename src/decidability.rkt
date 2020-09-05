#lang pie

(claim Dec
  (-> U U))
(define Dec
  (λ (X)
    (Either X
      (-> X Absurd))))

(claim zerop
  (-> Nat
      Atom))

(define nat=?
  (λ (n j)
    (ind-Nat j
      (λ (x) (Dec (= Nat n x)))
      (right (zero-not-add1 n))
      (λ (j-1 rest)
        (ind-Either rest
          (λ (e) (Dec (= Nat n j)))
          (λ (j-1=n) (right (use-Nat= n j-1)))
          (λ (ne-f) (ne-f )))))))












