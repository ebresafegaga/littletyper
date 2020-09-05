#lang pie

(claim + (-> Nat Nat Nat))
(define + (λ (x y) (iter-Nat x y (λ (result) (add1 result)))))

(claim id (Π ((X U)) (-> X X)))
(define id (λ (X x) x))

(claim llvm (-> Nat U))
(define llvm (λ (number) (Vec Atom number)))


(claim namer (Π ((l Nat)) (-> (Pair Atom Atom) (llvm l))))

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
     (λ (peas-n-1)
        (vec:: 'peas peas-n-1))))

(claim peas
       (Π ((number Nat))
          (Vec Atom number)))
(define peas
  (λ (number)
     (ind-Nat number
              mot-peas
              vecnil
              step-peas)))

(claim also-rec-Nat
       (Π ((X U))
          (-> Nat X (-> Nat X X)
             X)))
(define also-rec-Nat
  (λ (X)
     (λ (number base f)
        (ind-Nat number
                 (λ (k) X)
                 base
                 f))))

(claim base-last
       (Π ((E U))
          (-> (Vec E (add1 zero))
            E)))
(define base-last
  (λ (E)
     (λ (vec)
        (head vec))))

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
        (λ (es)
           (f (tail es))))))


(claim last
       (Π ((E U)
           (n Nat))
          (-> (Vec E (add1 n))
              E)))
(define last
  (λ (E n)
     (ind-Nat n
              (mot-last E)
              (base-last E)
              (step-last E))))

(claim baseDropLast
       (Π ((E U))
          (-> (Vec E (add1 zero))
              (Vec E zero))))
(define baseDropLast
  (λ (E)
     (λ (es) vecnil)))

(claim motiveDropLast
       (-> U Nat
           U))
(define motiveDropLast
  (λ (E l)
     (-> (Vec E (add1 l))
         (Vec E l))))

(claim stepDropLast
       (Π ((E U)
           (l Nat))
          (-> (motiveDropLast E l)
              (motiveDropLast E (add1 l)))))
(define stepDropLast
  (λ (E l)
     (λ (f)
        (λ (es)
           (vec:: (head es)
                  (f (tail es)))))))

(claim dropLast
       (Π ((E U)
           (l Nat))
          (-> (Vec E (add1 l))
              (Vec E l))))
(define dropLast
  (λ (E l)
     (ind-Nat l
              (motiveDropLast E)
              (baseDropLast E)
              (stepDropLast E))))

(claim gat TODO)


(claim map (Π ((E U) (B U)) (-> (List E) (-> E B) (List B))))
(define map
  (λ (E B)
     (λ (es f)
        (rec-List es
                  (the (List B) nil)
                  (λ (e es rest)
                     (:: (f e) rest))))))

(claim l (List Atom))
(define l (:: 'a (:: 'b (:: 'c (:: 'd (:: 'e nil))))))

(map Atom Nat l (λ (x) 1))

(claim incr (-> Nat Nat))

(define incr
  (λ (n)
     (iter-Nat 1
               0
               (+ 1))))

(= U Nat Atom)

(Π ((n Nat)) (= Nat (add1 n) (+ 1 n)))


(same (incr 2))

(claim +1=add1
       (Π ((n Nat))
          (= Nat (add1 n) (+ 1 n))))

(define +1=add1
  (λ (n)
     (same (add1 n))))

(claim base-incr=add1
       (= Nat (add1 zero) (incr zero)))
(define base-incr=add1
  (same (add1 zero))

(claim mot-incr=add1
       (-> Nat
           U))
(define mot-incr=add1
  (λ (n)
     (= Nat (add1 n) (incr n))))

(claim step-incr=add1
       (Π ((n Nat))
          (-> (= Nat
                (incr n)
                (add1 n))
              (= Nat
                 (add1
                   (incr n))
                 (add1
                   (add1 n))))))
;(define step-incr=add1
; (λ (n)
;    (λ (prev-proof)
;        (cong prev-proof (+ 1)))))
(claim mot-step-incr=add1 (-> Nat Nat Nat))
(define mot-step-incr=add1
  (λ (n k)
    (= Nat
      (add1 (incr n))
      (add1 k))))
 
(define step-incr=add1
  (λ (n)
    (λ (proof-n-1)
      (replace proof-n-1
        (mot-step-incr=add1 n)
        (same (add1 (incr n)))))))
  
  
(claim incr=add1
       (Π ((n Nat))
          (= Nat (add1 n) (incr n))))
define incr=add1
  (λ (n)
     (ind-Nat n
              mot-incr=add1
              base-incr=add1
              step-incr=add1)))

(claim mot-zip (Π ((A U)
                   (B U))
                  (-> Nat U)))
(define mot-zip
  (λ (A B)
     (λ (n)
        (-> (Vec A n) (Vec B n)
            (Vec (Pair A B) n)))))

(claim base-zip
       (Π ((A U)
           (B U))
          (-> (Vec A 0) (Vec B 0)
              (Vec (Pair A B) 0))))
(define base-zip
  (λ (A B)
     (λ (as bs)
        (the (Vec (Pair A B) 0)
             vecnil))))

(claim step-zip (Π ((A U)
                    (B U)
                    (n Nat))
                    (-> (mot-zip n)
                        (mot-zip (add1 n)))))
(define step-zip
  (λ (A B)
     (λ (n f)
        (λ (as bs)
           (vec:: (cons (head as) (head bs))
                  (f (tail as) (tail bs)))))))

(claim zip (Π ((n Nat)
               (A U)
               (B U))
              (-> (Vec A n) (Vec B n)
                  (Vec (Pair A B) n))))
(define zip
  (λ (n A B)
     (λ (as bs)
        (ind-Nat n
                 (mot-zip A B)
                 (base-zip A B)
                 (step-zip A B)))))

(claim double
  (-> Nat
    Nat))
(define double
  (λ (n)
    (iter-Nat n
      0
      (+ 2))))

(claim twice
  (-> Nat
    Nat))
(define twice
  (λ (n)
    (+ n n)))

(claim mot-add1+=+add1
  (-> Nat Nat
      U))
(define mot-add1+=+add1
  (λ (n k)
    (= Nat
      (add1 (+ n k))
      (+ n (add1 k)))))

(claim step-add1+=+add1
  (Π ((j Nat)
      (k Nat))
    (-> (mot-add1+=+add1 j k)
        (mot-add1+=+add1 j (add1 k)))))
(define step-add1+=+add1
  (λ (j k)
    (λ (proof-of-k-1)
      (cong proof-of-k-1 (+ 1)))))

(claim add1+=+add1
  (Π ((j Nat)
      (k Nat))
    (= Nat
       (add1 (+ n j))
       (+ n (add1 j)))))
(define add1+=+add1
  (λ (n j)
    (ind-Nat n
      (mot-add1+=+add1 j)
      (same (add1 j))
      (step-add1+=+add1 j))))

(claim mot-twice=double
  (-> Nat
      U))
(define mot-twice=double
  (λ (n)
    (= Nat
      (twice n)
      (double n))))

(claim step-twice=double
  (Π ((n Nat))
    (-> (mot-twice=double n)
        (mot-twice=double (add1 n)))))
(define step-twice=double
  (λ (n)
    (λ (prev-proof)
      (cong prev-proof (+ 1)))))

(claim twice=double
  (Π ((n Nat))
    (= Nat (twice n) (double n))))


(claim a (Π ((n Nat)
             (A U))
           (Vec A n)))
(define a (λ (nat A) (Vec A nat)))



(Σ ((A U))
  A)

(the (Σ ((A U))
       A)
  (cons (-> Nat
          Nat)
    (+ 7)))

(claim mot-zipWith (Π ((A U) (B U) (C U)) (-> Nat U)))
(define mot-zipWith (λ (A B C n) (-> (-> A B C) (Vec A n) (Vec B n) (Vec C n))))

(claim zipWith (Π ((A U) (B U) (C U) (n Nat)) (-> (-> A B C) (Vec A n) (Vec B n) (Vec C n))))
(define zipWith
  (λ
    (A B C n)
    (λ (f as bs)
      (ind-Nat n
        (mot-zipWith A B C)
        (λ (f as bs) (the (Vec C 0) vecnil)) (λ (num rest) (λ (f as bs) (vec:: (f (head as) (head bs)) (rest f (tail as) (tail as)))))))))

(claim zero+n=n (Π ((n Nat)) (= Nat (+ n 0) n)))
(define zero+n=n (λ (n) (ind-Nat n (λ (number) (= Nat (+ number 0) number)) (same 0) (λ (number proof) (cong proof (+ 1))))))










  
  

