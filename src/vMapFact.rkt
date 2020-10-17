#lang pie

(claim +
  (-> Nat Nat
      Nat))
(define +
  (λ (m n)
    (iter-Nat m
      n
      (λ (rest)
        (add1 rest)))))

(claim map
  (Π ((X U)
      (Y U)
      (n Nat))
    (-> (-> X Y) (Vec X n)
      (Vec Y n))))
(define map
  (λ (X Y n)
    (λ (f xs)
      (ind-Vec n xs
        (λ (k vs) (Vec Y k))
        vecnil
        (λ (k x xs ys)
          (vec:: (f x)
            ys))))))

(claim xs (Vec Nat 4))
(define xs
  (vec:: 10
    (vec:: 23
      (vec:: 45
        (vec:: 32 vecnil)))))

(claim ys (Vec Nat 4))
(define ys
  (vec:: 42
    (vec:: 21
      (vec:: 7
        (vec:: 3 vecnil)))))
 
(claim ++
  (Π ((X U)
      (m Nat)
      (n Nat))
    (-> (Vec X m) (Vec X n)
        (Vec X (+ m n)))))
(define ++
  (λ (X m n)
    (λ (ms ns)
      (ind-Vec m ms
        (λ (k ks) (Vec X (+ k n)))
        ns
        (λ (k x xs rest)
          (vec:: x rest))))))

(claim vMapFact
  (Π ((X U)
      (Y U)
      (m Nat)
      (n Nat)
      (f (-> X Y))
      (ms (Vec X m))
      (ns (Vec X n)))
    (= (Vec Y (+ m n))
       (map X Y (+ m n)
         f
         (++ X m n
           ms ns))
       (++ Y m n
         (map X Y m
           f ms)
         (map X Y n
           f ns)))))
(define vMapFact
  (λ (X Y m n)
    (λ (f ms ns)
      (ind-Vec m ms
        (λ (k ks) (= (Vec Y (+ k n))
                    (map X Y (+ k n)
                      f
                      (++ X k n
                        ks ns))
                    (++ Y k n
                      (map X Y k
                        f ks)
                      (map X Y n
                        f ns)))) 
        (same (map X Y n
                f ns))
        (λ (k x ks proof)
          (replace proof
             (λ (xs)
               (= (Vec Y (+ (add1 k) n))
                 (vec:: (f x)
                   (map X Y (+ k n)
                     f
                     (++ X k n
                       ks ns)))
                 (vec:: (f x) xs)))
          (same (vec:: (f x)
                   (map X Y (+ k n)
                     f
                     (++ X k n
                       ks ns))))))))))
