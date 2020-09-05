#lang pie

(claim step-list→vec
  (Π ((E U))
    (-> E (List E) (Σ ((l Nat)) (Vec E l))
        (Σ ((l Nat)) (Vec E l)))))
(define step-list→vec
  (λ (E e es rest)
    (cons (add1 (car rest))
      (vec:: e (cdr rest)))))


;(claim list→vec
;  (Π ((E U))
;    (-> (List E)
;        (Σ ((l Nat))
;          (Vec E l)))))
; (define list→vec
; (λ (E es)
;    (rec-List es
;     (cons 0 vecnil)
;      (step-list→vec E))))

(claim mot-replicate
  (-> U Nat
      U))
(define mot-replicate
  (λ (E l)
    (Vec E l)))

(claim step-replicate
  (Π ((E U)
      (e E)
      (l Nat))
    (-> (mot-replicate E l)
        (mot-replicate E (add1 l)))))
(define step-replicate
  (λ (E e l rest)
    (vec:: e rest)))

(claim replicate
  (Π ((E U) (l Nat))
    (-> E (Vec E l))))
(define replicate
  (λ (E l e)
    (ind-Nat l
      (mot-replicate E)
      (the (Vec E 0) vecnil)
      (step-replicate E e))))

(claim copy52
  (Π ((E U))
    (-> E (List E) (Σ ((l Nat)) (Vec E l))
        (Σ ((l Nat)) (Vec E l)))))
(define copy52
  (λ (E)
    (λ (e es rest)
      (cons 52 (replicate E 52 e)))))

(claim length
  (Π ((E U))
    (-> (List E)
        Nat)))
(define length
  (λ (E es)
    (rec-List es
      0
      (λ (e es' len-es)
        (add1 len-es)))))

(claim mot-list→vec
  (Π ((E U))
    (-> (List E)
        U)))
(define mot-list→vec
  (λ (E es)
    (Vec E (length es))))

(claim list→vec
  (Π ((E U)
      (es (List E)))
    (Vec E (length es))))
(define list→vec
  (λ (E es)
    (ind-List es
      (mot-list→vec E)
      (the (Vec E 0) vecnil)
      (λ (e es rest) (vec:: e rest)))))

(claim treats
  (Vec Atom 3))
(define treats
  (vec:: 'kanleeee
    (vec:: 'another
      (vec:: 'another vecnil))))

(claim drinks (List Atom))
(define drinks
  (:: 'one
    (:: 'two nil)))

(claim +
  (-> Nat Nat
    Nat))
(define +
  (λ (a b)
    (rec-Nat b
      a
      (λ (_ rest) (add1 rest)))))

(claim mot-vec-append
  (Π ((E U)
      (a Nat)
      (b Nat))
    (-> (Vec E b)
        U)))
(define mot-vec-append
  (λ (E a)
    (λ (b es)
      (Vec E (+ a b)))))

(claim step-vec-append
  (Π ((E U)
      (j Nat)
      (k Nat)
      (e E)
      (es (Vec E k)))
    (-> (mot-vec-append E j k es)
        (mot-append E j (add1 k) (vec:: e es)))))
(define step-vec-append
  (λ (E e j k es rest)
    (vec:: e rest)))

(claim vec-append
  (Π ((E U)
      (a Nat)
      (b Nat))
    (-> (Vec E a) (Vec E b)
        (Vec E (+ a b)))))
(define vec-append
  (λ (E a b)
    (λ (es end)
      (ind-Vec l es
        (mot-vec-append E l)
        end
        (step-vec-append E l)))))

(claim mot-vec→list
  (Π ((E U)
      (k Nat))
    (-> (Vec E k)
        U)))
(define mot-vec→list
  (λ (E k es)
    (List E)))

(claim step-vec→list
  (Π ((E U)
      (k Nat)
      (e E)
      (es (Vec E k)))
    (-> (mot-vec→list E k es)
        (mot-vec→list E k (vec:: e es)))))
(define step-vec→list
  (λ (E k e es rest)
    (:: e rest)))

(claim vec→list
  (Π ((E U)
      (k Nat))
    (-> (Vec E k)
        (List E))))
(define vec→list
  (λ (E k es)
    (ind-Vec k es
      (mot-vec→list E)
      nil
      (step-vec→list E))))

(claim mot-list→vec→list=
  (Π ((E U))
    (-> (List E)
        U)))
(define mot-list→vec→list=
  (λ (E es)
    (= (List E) es (vec→list E (length es) (list→vec E es))))

(claim Treat-Statement U)
(define Treat-Statement
  (Π ((some (List Atom))
      (more (List Atom)))
    (-> (= (List Atom) some more)
        (= (List Atom)
          (:: 'platter some)
          (:: 'platter more)))))
  
(claim ::-platter
  (-> (List Atom)
    (List Atom)))
(define ::-platter
  (λ (es)
    (:: 'platter es)))

(claim proof=:: Treat-Statement)
(define proof=::
  (λ (this that)
    (λ (proof-eq)
      (cong proof-eq ::-platter))))

(claim proof-length=
  (Π ((this (List Atom))
      (that (List Atom)))
    (-> (= (List Atom) this that)
        (= Nat (length Atom this) (length Atom that)))))
(define proof-length=
  (λ (this that)
    (λ (proof=)
      (cong proof= (length Atom)))))(

(claim conser
  (Π ((E U)))
    (-> (List E) E (List E))))
(define conser
  (λ (E e es)
    (:: e es)))


(claim step-list→vec→list=
  (Π ((E U)
      (e E)
      (es (List E)))
    (-> (mot-list→vec→list= E es)
        (mot-list→vec→list= E (:: e es)))))
(define step-list→vec→list=
  (λ (E e es proof-es)
    (cong proof-es (conser E e))))


(claim list→vec→list=
  (Π ((E U)
      (es (List E)))
    (= (List E)
       es
       (vec→list E (length es) (list→vec E es)))))
(define list→vec→list=
  (λ (E es)
    (ind-List es
      (mot-list→vec→list= E)
      (the (= (List E) nil nil) (same nil))
      (step-list→vec→list= E))))







