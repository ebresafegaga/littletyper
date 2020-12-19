#lang pie

;; It's all about the motive

(claim mot-peas
  (-> Nat
      U))
(define mot-peas
  (λ (k)
    (Vec Atom k)))

(claim step-peas
  (Π ((l-1 Nat))
    (-> (mot-peas l-1)
        (mot-peas (add1 l-1)))))
(define step-peas
  (λ (l-1)
    (λ (xs)
      (vec:: 'peas xs))))

(claim peas
  (Π ((how-many Nat))
    (Vec Atom how-many)))
(define peas
  (λ (how-many)
    (ind-Nat how-many
      mot-peas
      vecnil
      step-peas)))

(claim base-last
  (Π ((E U))
    (-> (Vec E (add1 zero))
        E)))
(define base-last
  (λ (E)
    (λ (xs)
      (head xs))))

(claim mot-last
  (-> U Nat
      U))
(define mot-last
  (λ (E k)
    (-> (Vec E (add1 k))
        E)))

(claim step-last
  (Π ((E U)
      (l-1 Nat))
    (-> (mot-last E l-1)
        (mot-last E (add1 l-1)))))
(define step-last
  (λ (E l-1)
    (λ (f)
      (λ (es) (f (tail es))))))

(claim last
  (Π ((E U)
      (l Nat))
    (-> (Vec E (add1 l))
        E)))
(define last
  (λ (E l)
    (ind-Nat l
      (mot-last E)
      (base-last E)
      (step-last E))))

(claim base-drop-last
  (Π ((E U))
    (-> (Vec E (add1 zero))
        (Vec E zero))))
(define base-drop-last
  (λ (E)
    (λ (xs)
      vecnil)))

(claim mot-drop-last
  (-> U Nat
      U))
(define mot-drop-last
  (λ (E k)
    (-> (Vec E (add1 k))
        (Vec E k))))

(claim step-drop-last
  (Π ((E U)
      (l-1 Nat))
    (-> (mot-drop-last E l-1)
        (mot-drop-last E (add1 l-1)))))
(define step-drop-last
  (λ (E l-1)
    (λ (g)
      (λ (es)
        (vec:: (head es)
          (g (tail es)))))))
