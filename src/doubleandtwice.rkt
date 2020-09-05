#lang pie

(claim +
  (-> Nat Nat
    Nat))
(define +
  (λ (a b)
    (iter-Nat b
      a
      (λ (rest)
        (add1 rest)))))

(claim double
  (-> Nat Nat))
(define double
  (λ (k)
    (iter-Nat k
      0
      (λ (rest)
        (add1 (add1 rest))))))

(claim twice
  (-> Nat
    Nat))
(define twice
  (λ (n) (+ n n)))

(claim Even
  (-> Nat
      U))
(define Even
  (λ (k)
    (Σ ((half Nat))
      (= Nat k (double half)))))

(claim zero-is-even
  (Even 0))
(define zero-is-even
  (cons 0
    (same 0)))

(claim +two-even
  (Π ((n Nat))
    (-> (Even n)
        (Even (+ n 2)))))
(define +two-even
  (λ (n)
    (λ (even-n)
      (cons (add1 (car even-n))
        (cong (cdr even-n) (+ 2))))))


(claim Odd
  (-> Nat
    U))
(define Odd
  (λ (k)
    (Σ ((haf Nat))
      (= Nat k (add1 (double haf))))))

(claim add1-even→odd
  (Π ((n Nat))
    (-> (Even n)
        (Odd (add1 n)))))
(define add1-even→odd
  (λ (n even)
    (cons (car even)
      (cong (cdr even) (+ 1)))))

(claim add1-odd→even
  (Π ((n Nat))
    (-> (Odd n)
        (Even (add1 n)))))
(define add1-odd→even
  (λ (n odd)
    (cons (add1 (car odd))
      (cong (cdr odd) (+ 1)))))

(claim repeat
  (-> (-> Nat Nat)
      Nat
      Nat))
(define repeat
  (λ (f n)
    (iter-Nat n
      (f 1)
      (λ (rest) (f rest)))))


(claim ackerman
  (-> Nat Nat
      Nat))
(define ackerman
  (λ (n)
    (iter-Nat n
      (+ 1)
      (λ (rest) (repeat rest)))))


(left 10)

(claim mot-even-or-odd
  (-> Nat
      U))
(define mot-even-or-odd
  (λ (n)
    (Either (Even n) (Odd n))))

(claim step-even-or-odd
  (Π ((n Nat))
    (-> (mot-even-or-odd n)
        (mot-even-or-odd (add1 n)))))
(define step-even-or-odd
  (λ (k)
    (λ (proof)
      (ind-Either proof
        (λ (p) (mot-even-or-odd k))
        (λ (even) (right (add1-even→odd k even)))
        (λ (odd) (left (add1-odd→even k odd)))))))

(claim even-or-odd
  (Π ((N Nat))
    (Either (Even n) (Odd n))))
(define even-or-odd
  (λ (n)
    (ind-Nat n
      mot-even-or-odd
      (left zero-is-even)
      step=even-or-odd)))




















