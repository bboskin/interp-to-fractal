#lang racket

(require rackunit)

(provide (all-defined-out))

;; Structs for return value types

(struct True ())
(struct False ())
(struct Empty ())


(struct Add1 (n) #:transparent)
(struct Sub1 (n) #:transparent)
(struct Car (p) #:transparent)
(struct Cdr (p) #:transparent)
(struct Zero? (n)  #:transparent)
(struct Null? (n)  #:transparent)

(struct Cons (a d) #:transparent)
(struct If (t c a) #:transparent)

(struct Plus (xs) #:transparent)
(struct Times (xs) #:transparent)
(struct And (xs) #:transparent)
(struct Or (xs) #:transparent)

(struct Less-Than (n m) #:transparent)
(struct Greater-Than (n m) #:transparent)
(struct Less-Than-= (n m) #:transparent)
(struct Greater-Than-= (n m) #:transparent)

(define (unary n) (if (<= n 0) n `(add1 ,(unary (sub1 n)))))
(define always-true (λ (x) #t))
(define always-false (λ (x) #f))
(define (coerce-bool f) (λ (x) (if (f x) (True) (False))))
(define (Boolean? x)
  (or (True? x) (False? x)))



;; Environments
(define (empty-env) '())
(define (apply-env env y)
  (let ((pr (assv y env)))
    (if pr (cdr pr) (cons y y))))
(define (extend-env x e a env)
  (cons (cons x (cons e a)) env))
(define (extend-env* xs es as env)
  (cond
    ((and (null? xs) (null? as)) env)
    ((or (null? xs) (null? as)) (error 'extend-env* "mismatched arities"))
    (else (extend-env* (cdr xs) (cdr es) (cdr as) (extend-env (car xs) (car es) (car as) env)))))


;; Closures
(struct Closure (xs env b))
(define make-closure Closure)

(define (apply-closure c es vs)
  (match c
    [(Closure xs env b)
     ((expand (extend-env* xs es vs env)) b)]
    [else (cons (cons c es) (cons c es))]))

;; Evaluation/expansion

;; expects op to be commutative
(define (crunch pred? sym op base ls)
  (let loop ((ans base)
             (ls ls)
             (kept '()))
    (cond
      [(null? ls) (if (null? kept) ans (sym (cons ans (reverse kept))) #;`(,sym ,ans . ,(reverse kept)))]
      [(pred? (car ls)) (loop (op (car ls) ans) (cdr ls) kept)]
      [else (loop ans (cdr ls) (cons (car ls) kept))])))

;; helpers for certain ops

(define (if-c env t c a)
  (let ((res ((expand env) c)))
    (cons `(if #t ,t ,(car res) ,a) (cdr res))))

(define (if-a env t c a)
  (let ((res ((expand env) a)))
    (cons `(if #f ,t ,c ,(car res)) (cdr res))))

(define (do-if env t c a)
  (let* ((res-t ((expand env) t))
         (t-e (car res-t))
         (t-a (cdr res-t)))
    (if (Boolean? t-a)
        (if (True? t-a)
            (if-c env t-e c a)
            (if-a env t-e c a))
        (cons `(if unsure ,t-e ,c ,a) (If t-a c a)))))

(define (do-closure xs b env)
  (cons `(λ ,xs ,(car ((expand env) b)))
        (make-closure xs env b)))

(define (do-and x y)
  (if (or (False? x) (False? y)) (False) (True)))

(define (do-or x y)
  (if (and (False? x) (False? y)) (False) (True)))

(define (do-cons env a d)
  (let ((res1 ((expand env) a))
        (res2 ((expand env) d)))
    (cons `(cons ,(car res1) ,(car res2))
          (Cons (cdr res1) (cdr res2)))))

(define (do-comp n m comp comp-constr env)
  (let ((res-n ((expand env) n))
        (res-m ((expand env) m)))
    (cons `(< ,(car res-n) ,(car res-m))
          (goo
              (((number? number?) (λ (a b) (if (comp a b) (True) (False))))
               ((always-true always-true) (λ (e1 e2) (comp-constr e1 e2))))
              ((cdr res-n) (cdr res-m))))))

(define-syntax do-unary
  (syntax-rules ()
    ((_ env sym name go ...)
     (let ((res ((expand env) name)))
       (cons `(sym ,(car res))
             (goo (go ...)
                  (cdr res)))))))

(define-syntax do-arb-arity
  (syntax-rules ()
    ((_ env pred? sym ms Con op b)
     (let ((es/vs (map (expand env) ms)))
       (cons `(sym . ,(map car es/vs))
             (crunch pred? Con op b (map cdr es/vs)))))))

(define-syntax goo
  (syntax-rules ()
    ((_ () vs) (error 'no-valid-option))
    ((_ (((cases ...) res1) e ...) (vs ...))
     (if (and (cases vs) ...)
         (res1 vs ...)
         (goo (e ...) (vs ...))))
    ((_ ((case res1) e ...) v)
     (if (case v)
         (res1 v)
         (goo (e ...) v)))))

(define ((expand env) exp)
  (match exp
    ['empty (cons 'empty (Empty))]
    [(? boolean? b) (cons b (if b (True) (False)))]
    [(? number? n) (cons (unary n) n)]
    [(? symbol? y) (apply-env env y)]
    [`(λ (,xs ...) ,b) (do-closure xs b env)]
    [`(< ,n ,m) (do-comp n m < Less-Than env)]
    [`(<= ,n ,m) (do-comp n m <= Less-Than-= env)]    
    [`(> ,n ,m) (do-comp n m > Greater-Than env)]
    [`(>= ,n ,m) (do-comp n m >= Greater-Than-= env)]
    [`(add1 ,k) (do-unary env add1 k (number? add1) (Sub1? Sub1-n) (always-true Add1))]
    [`(sub1 ,k) (do-unary env sub1 k (number? sub1) (Add1? Add1-n) (always-true Sub1))]
    [`(zero? ,n) (do-unary env zero? n (number? (coerce-bool zero?)) (always-true Zero?))]
    [`(null? ,ls) (do-unary env null? ls (Cons? (λ (_) (False))) (Empty? (λ (_) (True))) (always-true Null?))]
    [`(cons? ,pr) (do-unary env cons? pr (Null? (λ (_) (False))) (Cons? (λ (_) (True))) (always-true Cons?))]
    [`(car ,pr) (do-unary env car pr (Cons? Cons-a) (always-true Car))]
    [`(cdr ,pr) (do-unary env cdr pr (Cons? Cons-d) (always-true Cdr))]
    [`(+ ,ms ...) (do-arb-arity env number? + ms Plus + 0)]
    [`(* ,ms ...) (do-arb-arity env number? * ms Times * 1)]
    [`(and ,ms ...) (do-arb-arity env always-true and ms And do-and (True))]
    [`(or ,ms ...) (do-arb-arity env always-true or ms Or do-or (False))]
    [`(cons ,a ,d) (do-cons env a d)]
    [`(if ,t ,c ,a) (do-if env t c a)]
    [`(let ,es ,b)
     (let ((res* (map (expand env) (map cadr es))))
       ((expand (extend-env* (map car es) (map car res*) (map cdr res*) env)) b))]
    [`(,f ,xs ...)
     (let* ((xs (map (expand env) xs))
            (xs-es (map car xs))
            (xs-as (map cdr xs))
            (f ((expand env) f))
            (r (apply-closure (cdr f) xs-es xs-as))
            (e^ (car r))
            (a^ (cdr r)))
       (cons `(app ,e^ . ,xs-es) a^))]))

(define (make-defs env defs)
  (match defs
    ['() env]
    [`((define ,name ,d) . ,rst)
     (let* ((b ((expand env) d))
            (env (extend-env name (car b) (cdr b) env)))
       (make-defs env rst))]))

(define (run defs c)
  (let* ((env (make-defs (empty-env) defs))
         (x ((expand env) c)))
    (print (cdr x))
    (car x)))

(define (run-val defs c)
  (let* ((env (make-defs (empty-env) defs))
         (x ((expand env) c)))
    (cdr x)))

;; factorial

(define (fact-of1 n)
  `(((λ (f) (λ (g) ((f f) g)))
     (λ (fact) (λ (k) (if (zero? k) 1 (* k ((fact fact) (sub1 k)))))))
    ,n))

(define (fact-of2 n)
  `(((λ (f) (λ (g a) ((f f) g a)))
     (λ (fact) (λ (k a) (if (zero? k) a ((fact fact) (sub1 k) (* k a))))))
    ,n 1))

(define (fact-of3 n)
  `(let ((fact (λ (fact) (λ (k) (if (zero? k) 1 (* k ((fact fact) (sub1 k))))))))
     (((λ (f) (λ (g) ((f f) g))) fact) ,n)))


(define (fact-of4 n)
  `(let ((fact (λ (fact)
                 (λ (v k)
                   (if (zero? v) (k 1)
                       ((fact fact) (sub1 v) (λ (a) (* v (k a)))))))))
     (((λ (f) (λ (n k) ((f f) n k)))
       fact)
      ,n (λ (x) x))))

(define p1
  '((define fact
      ((λ (f) (λ (g) ((f f) g)))
       (λ (fact) (λ (k) (if (zero? k) 1 (* k ((fact fact) (sub1 k))))))))))

#;
(check-equal? (run p1 '(fact 5))
              (run '() (fact-of1 5)))

(check-equal? (run-val '() (fact-of1 5)) 120)
(check-equal? (run-val '() (fact-of2 5)) 120)
(check-equal? (run-val '() (fact-of3 5)) 120)
(check-equal? (run-val '() (fact-of4 5)) 120)


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

(check-equal? #t (True? (run-val '() (even? 6))))
(check-equal? #f (True? (run-val '() (even? 7))))

(define l1
  '(cons 4 (cons 3 (cons 9 (cons 12 (cons 0 (cons -3 empty)))))))


(define (insert l)
  `(let ((insert
             (λ (insert)
               (λ (x l)
                 (if (null? l)
                     (cons x empty)
                     (if (< x (car l))
                         (cons x l)
                         (cons (car l) ((insert insert) x (cdr l)))))))))
     (((λ (f) (λ (g k) ((f f) g k))) insert) 5 ,l)))

(check-equal? (Cons-a (Cons-d (Cons-d (run-val '() (insert '(cons 3 (cons 4 (cons 6 empty)))))))) 5)

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

(check-equal? (Cons-a (run-val '() (isort l1))) -3)

(define (selsort l)
  `(let ((find-min
          (λ (find-min)
            (λ (curr rst l)
              (if (null? l)
                  (cons curr rst)
                  (if (< curr (car l))
                      ((find-min find-min) curr (cons (car l) rst) (cdr l))
                      ((find-min find-min) (car l) (cons curr rst) (cdr l))))))))
     (let ((selsort
            (λ (selsort)
              (λ (ls)
                (if (null? ls)
                    empty
                    (let ((choose (((λ (f) (λ (g1 g2 g3) ((f f) g1 g2 g3))) find-min)
                                   (car ls) empty (cdr ls))))
                      (cons (car choose) ((selsort selsort) (cdr choose)))))))))
       (((λ (f) (λ (g) ((f f) g))) selsort) ,l))))

(check-equal? (Cons-a (run-val '() (selsort l1))) -3)

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

(check-equal? (Cons-a (run-val '() (qsort l1))) -3)
(check-equal? #t (Empty? (run-val '() (qsort 'empty))))

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

(check-equal? (Cons-a (run-val '() (msort l1))) -3)
(check-equal? #t (Empty? (run-val '() (msort 'empty))))

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
  (if (zero? n)
      (add1 m)
      (if (zero? m)
          (ack (sub1 n) 1)
          (ack (sub1 n) (ack n (sub1 m))))))


