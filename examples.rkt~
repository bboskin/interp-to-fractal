#lang racket

(require "animate-code.rkt" "expander.rkt")

(provide (all-defined-out))

;; numbers
(define (G k n m)
  `(let ((G (λ (G)
              (λ (k n m)
                (if (zero? m)
                    (if (zero? k)
                        n
                        (if (zero? (sub1 k)) 0 1))
                    (if (zero? k)
                        (add1 ((G G) k n (sub1 m)))
                        ((G G) (sub1 k) n ((G G) k n (sub1 m)))))))))
     (((λ (f) (λ (k n m) ((f f) k n m))) G)
      ,k ,n ,m)))

(define (ack n m)
  `(let ((ack
          (λ (ack)
            (λ (n m)
              (if (zero? n)
                  (add1 m)
                  (if (zero? m)
                      ((ack ack) (sub1 n) 1)
                      ((ack ack) (sub1 n) ((ack ack) n (sub1 m)))))))))
     (((λ (f) (λ (n m) ((f f) n m))) ack) ,n ,m)))

(define (even? n)
  `(let ((meven?
             (λ (meven? modd?)
               (λ (n) (if (zero? n) #t
                          ((modd? meven? modd?) (sub1 n))))))
            (modd?
             (λ (meven? modd?)
               (λ (n) (if (zero? n) #f
                          ((meven? meven? modd?) (sub1 n)))))))
     (((λ (f g) (λ (n) ((f f g) n))) meven? modd?) ,n)))


;; sorting
(define (msort l)
  `(let ((split
          (λ (split)
            (λ (ls a b)
              (if (null? ls) (cons a b)
                  ((split split) (cdr ls) (cons (car ls) b) a)))))
         (merge
          (λ (merge)
            (λ (l1 l2)
              (if (null? l1) l2
                  (if (null? l2) l1
                      (if (< (car l1) (car l2))
                          (cons (car l1) ((merge merge) (cdr l1) l2))
                          (cons (car l2) ((merge merge) l1 (cdr l2))))))))))
     (let ((msort
            (λ (msort)
              (λ (ls)
                (if (or (null? ls) (null? (cdr ls)))
                    ls
                    (let ((s (((λ (f) (λ (l a b) ((f f) l a b))) split) ls empty empty)))
                      (let ((r1 ((msort msort) (car s)))
                            (r2 ((msort msort) (cdr s))))
                        (((λ (f) (λ (g1 g2) ((f f) g1 g2))) merge) r1 r2))))))))
       (((λ (f) (λ (g) ((f f) g))) msort) ,l))))

(define (qsort l)
  `(let ((partition
          (λ (partition)
            (λ (pivot l ge ls)
              (if (null? ls)
                  (cons l ge)
                  (if (< (car ls) pivot)
                      ((partition partition) pivot (cons (car ls) l) ge (cdr ls))
                      ((partition partition) pivot l (cons (car ls) ge) (cdr ls)))))))
         (append
          (λ (append)
            (λ (l1 l2)
              (if (null? l1) l2
                  (cons (car l1) ((append append) (cdr l1) l2)))))))
     (let ((qsort
            (λ (qsort)
              (λ (l)
                (if (null? l)
                    empty
                    (let ((piv (car l)))
                      (let ((res (((λ (f) (λ (p l g ls) ((f f) p g l ls))) partition)
                                  piv empty empty (cdr l))))
                        (((λ (f) (λ (l1 l2) ((f f) l1 l2))) append) ((qsort qsort) (car res))
                                (cons piv ((qsort qsort) (cdr res)))))))))))
       (((λ (f) (λ (g) ((f f) g))) qsort)
        ,l))))

(define (isort l)
  `(let ((insert
          (λ (insert)
            (λ (x l)
              (if (null? l)
                  (cons x empty)
                  (if (< x (car l))
                      (cons x l)
                      (cons (car l) ((insert insert) x (cdr l)))))))))
     (let ((isort
            (λ (isort)
              (λ (ls)
                (if (null? ls)
                    empty
                    (((λ (f) (λ (g h) ((f f) g h))) insert)
                     (car ls)
                     ((isort isort) (cdr ls))))))))
       (((λ (f) (λ (g) ((f f) g))) isort) ,l))))


;;;;; Random things

(define (foo1 n m)
  `(let ((foo (λ (foo goo)
               (λ (k l n m o p)
                 (if (zero? k)
                     (* l n m o p)
                     ((goo foo goo) (sub1 k) (add1 l) (+ n m) (+ m o) (+ o p) 2)))))
        (goo (λ (foo goo)
               (λ (k l n m o p)
                 (if (zero? k)
                     (+ l n m o p)
                     ((foo foo goo) (sub1 k) (add1 l) (* n m) (* m o) (* o p) 1))))))
     (((λ (f g) (λ (a b c d e h) ((f f g) a b c d e h))) foo goo)
      ,n ,m 1 1 1 1)))