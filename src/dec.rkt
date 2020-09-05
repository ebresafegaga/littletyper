#lang pie

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

(claim =consequnce-same
  (Π ((N Nat))
    (=consequnce n n)))
(define =consequnce-same
  (λ (n)
    (ind-Nat n
      (λ (k) (=consequnce k k))
      sole
      (λ (n-1 rest) (same n-1)))))


(claim use-Nat=
  (Π ((n Nat)
      (j Nat))
    (-> (= Nat n j)
        (=consequence n j))))
(define use-Nat=
  (λ (n j)
    (λ (n=j)
      (replace n=j
        (λ (k) (=consequence n k))
        (=consequence-same n)))))

(claim zero-not-add1
  (Π ((n Nat))
    (-> (= Nat zero (add1 n))
        Absurd)))
(define zero-not-add1
  (λ (n)
    (use-Nat= zero (add1 n))))

(claim donut-absurdity
  (-> (= Nat 0 6)
      (= Atom 'powdered 'glazed)))
(define donut-absurdity
  (λ (zero=six)
    (ind-Absurd
      (zero-not-add1 5 zero=six)
      (= Atom 'powdered 'glazed))))

(claim sub1=
  (Π ((a Nat)
      (b Nat))
    (-> (= Nat (add1 a) (add1 b))
        (= Nat a b))))
(define sub1
  (λ (a b)
    (use-Nat= (add1 a) (add1 b))))


(claim one-not-six
  (-> (= Nat 1 6)
      Absurd))
(define one-not-six
  (λ (one=six)
    (zero-not-add1 4 (sub1= 0 5 one=six))))


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
    (λ (f)
      (λ (j l+=add1-j) e))))


;; A similar technique is used to
;; write drop-last or rest using ind-Vec

(claim front
  (Π ((E U)
      (n Nat))
    (-> (Vec E (add1 n))
        E)))
(define front
  (λ (E)
    (λ (n es)
      ((ind-Vec (add1 n) es
         (mot-front E)
         (λ (j eq) (ind-Absurd (zero-not-add1 j eq) E))
         (step-front E))
        n (same add1 n)))))


(claim pem
  (Π ((X U))
    (Either X
            (-> X Absurd))))

(claim pem-not-false
  (Π ((X U))
    (-> (-> (Either X (-> X Absurd))
            Absurd)
        Absurd)))
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      (pem-false
        (right
          (λ (x)
            (pem-false
              (left x))))))))

(claim Dec
  (-> U U))
(define Dec
  (λ (X)
    (Either X
      (-> X Absurd))))

(define zerop
  (λ (x)
    (which-Nat x
      't
      'nil)))

(claim zero?
  (Π ((j Nat))
    (Dec
     (= Nat zero j))))
(define zero?
  (λ (j)
    (ind-Nat j
      (λ (x) (Dec (= Nat zero x)))
      (left (same zero))
      (λ (n-1 rest)
        (right
          (zero-not-add1 n-1))))))

(claim add1-not-zero
  (Π ((n Nat))
    (-> (= Nat (add1 n) zero)
        Absurd)))
(define add1-not-zero
  (λ (n)
    (use-Nat= (add1 n) zero)))

(claim dec-add1=
  (Π ((n Nat)
      (k Nat))
    (-> (Dec (= Nat n k))
        (Dec (= Nat (add1 n) (add1 k))))))
(define dec-add1=
  (λ (n k)
    (λ (maybe-n=k)
      (ind-Either maybe-n=k
        (λ (target) (Dec (= Nat (add1 n) (add1 k))))
        (λ (yes) (cong yes (+ 1)))
        (λ (no)
          (right
            (λ (n=k)
              (no (sub1= n k n=k)))))))))

(claim mot-nat=?
  (-> Nat
    U))
(define mot-nat=?
  (λ (n)
    (Π ((j Nat))
      (Dec
       (= Nat n j)))))

(claim step-nat=?
  (Π ((n Nat))
    (-> (mot-nat=? n)
        (mot-nat=? (add1 n)))))
(define step-nat=?
  (λ (n)
    (λ (nat=?-n-1)
      (λ (k)
        (ind-Nat k
          (λ (j) (Dec (= Nat (add1 n) j)))
          (right (add1-not-zero n))
          (λ (k-1 r)
            (dec-add1= n k-1 (nat=?-n-1 k-1))))))))


(claim nat=?
  (Π ((n Nat)
      (j Nat))
    (Dec
     (= Nat n j))))
(define nat=?
  (λ (n j)
    ((ind-Nat n
       TODO
       TODO
       TODO)
      j)))






















