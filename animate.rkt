#lang racket

(require 2htdp/image "expander.rkt")
(provide main)

(define (base? x)
  (ormap (λ (f) (f x)) (list number? symbol? boolean? empty?)))
(define (binary-op? x)
  (memv x '(cons > >= < <=)))
(define (unary-op? x)
  (memv x '(add1 car cdr zero? null? cons? sub1 gray in)))
(define (arb-op? x) (memv x '(and or + *)))

(define (depth e)
  (match e
    [(? boolean? b) 1]
    [(? number? k) 1]
    ['empty 1]
    [(? symbol? y) 1]
    ['(blank) 1]
    [`(,(? unary-op? o) ,d ,e) d]
    [`(,(? binary-op? o) ,d ,e1 ,e2) d]
    [`(,(? arb-op? o) ,d . ,es) d]
    [`(if ,d ,v ,t ,c ,a) d]
    [`(λ ,xs ,b) 1]
    [`(app ,d ,res-exp . ,args) d]
    ;; forms for code which won't be zoomed into (may occur in unused if branches and unapplied lambdas)
    [`(,(? unary-op? o) ,e) 1]
    [`(,(? binary-op? o) ,e1 ,e2) 2]
    [`(,(? arb-op? o) . ,es) (length es)]
    [`(if ,t ,c ,a) (+ (depth t) (depth c) (depth a))]
    [`(let ,ds ,b) (depth b)]
    [`(,f . ,vs) (add1 (length vs))])
  #;
  (match e
    [`(,(? unary-op?) ,x) (depth x)]
    [`(,(? binary-op?) ,a ,d) (+ (depth a) (depth d))]
    [`(if ,v . ,es) (foldr (λ (x a) (+ (depth x) a)) 0 es)]
    [`(,(? arb-op?) . ,xs) (foldr (λ (x a) (+ (depth x) a)) 0 xs)]
    [`(λ ,xs ,b) (depth b)]
    [`(let ,xs ,b) (+ (depth b) (foldr (λ (x a) (+ (depth (cadr x)) a)) 0 xs))]
    [`(,f . ,xs) (+ (depth f) (foldr (λ (x a) (+ (depth x) a)) 0 xs))]
    [else 1]))

(define (subimg C ty)
  (match C
    [(? boolean? b) (values #f 'boolean)]
    [(? number? k) (values #f 'number)]
    ['empty (values #f 'list)]
    [(? symbol? y) (values #f ty)]
    ['(blank) (values #f ty)]
    [`(with-depth ,(? unary-op? o) ,d ,e) (values e (car (op->argtys o)))]
    [`(with-depth ,(? binary-op? o) ,d ,e1 ,e2)
     (values (if (>= (depth e1) (depth e2)) e1 e2)
             (car (op->argtys o)))]
    [`(with-depth ,(? arb-op? o) ,d . ,es)
     (let-values (((e) (find-largest-depth/expr es)))
       (values e (car (op->argtys o))))]
    [`(with-depth if ,d #t ,t ,c ,a) (values c ty)]
    [`(with-depth if ,d #f ,t ,c ,a) (values a ty)]
    [`(with-depth if ,d ,v ,t ,c ,a) (values (if (>= (depth c) (depth a)) c a) ty)]
    [`(λ ,xs ,b) (values b 'any)]
    [`(with-depth app ,d ,res-exp . ,args) (values res-exp ty)]
    ;; forms for code which won't be zoomed into (may occur in unused if branches and unapplied lambdas)
    [`(,(? unary-op? o) ,e) (values e (car (op->argtys o)))]
    [`(,(? binary-op? o) ,e1 ,e2)
     (values (if (>= (depth e1) (depth e2)) e1 e2)
             (car (op->argtys o)))]
    [`(,(? arb-op? o) . ,es)
     (let-values (((e) (find-largest-depth/expr es)))
       (values e (car (op->argtys o))))]
    [`(if #t ,t ,c ,a) (values c ty)]
    [`(if #f ,t ,c ,a) (values a ty)]
    [`(if ,v ,t ,c ,a) (values (if (>= (depth c) (depth a)) c a) ty)]
    [`(if ,t ,c ,a) (values (if (>= (depth c) (depth a)) c a) ty)]
    [`(λ ,xs ,b) (values b 'any)]
    [`(let ,ds ,b) (values b ty)]
    [`(app ,res-exp . ,args) (values res-exp ty)]
    [`(,f . ,vs) (values f 'function)])
  #;(match C
    [(? boolean? b) (values #f 'boolean)]
    [(? number? k) (values #f 'number)]
    ['empty (values #f 'list)]
    ['(blank) (values #f ty)]
    [(? symbol? y) (values #f ty)]
    [`(,(? unary-op? o) ,e) (values e (car (op->argtys o)))]
    [`(,(? binary-op? o) ,e1 ,e2)
     (values (if (>= (depth e1) (depth e2)) e1 e2)
             (car (op->argtys o)))]
    [`(,(? arb-op? o) . ,es)
     (let-values (((e) (find-largest-depth/expr es)))
       (values e (car (op->argtys o))))]
    [`(if #t ,t ,c ,a) (values c ty)]
    [`(if #f ,t ,c ,a) (values a ty)]
    [`(if ,v ,t ,c ,a) (values (if (>= (depth c) (depth a)) c a) ty)]
    [`(if ,t ,c ,a) (values (if (>= (depth c) (depth a)) c a) ty)]
    [`(λ ,xs ,b) (values b 'any)]
    [`(let ,ds ,b) (values b ty)]
    [`(app ,res-exp . ,args) (values res-exp ty)]
    [`(,f . ,vs) (values f 'function)]))


(define (insert-at x l k)
  (cond
    [(zero? k) (cons x l)]
    [(null? l) (list x)]
    [else (cons (car l) (insert-at x (cdr l) (sub1 k)))]))

(define (split k ls)
  (cond
    ((null? ls) '())
    ((< (length ls) k) (list ls))
    (else (cons (take ls k) (split k (drop ls k))))))

(define-syntax just-image
  (syntax-rules ()
    ((_ e) (let-values (((res c size) e)) res))))

;; color constants
(define TEXT-COLOR "white")
(define TRANSPARENT (color 0 0 0 0))
(define ANYTHING-COLOR "white")
(define BACKGROUND-COLOR "black")
(define NUMBER-COLOR "red")
(define BOOLEAN-COLOR "blue")
(define FUNCTION-COLOR "green")
(define LIST-COLOR "purple")
(define TRANSLUCENT-GRAY (color 150 150 150 150))


;; colors associated to operations and types

(define TYPE-COLOR-LIST
  `((list . ,LIST-COLOR)
    (number . ,NUMBER-COLOR)
    (boolean . ,BOOLEAN-COLOR)
    (function . ,FUNCTION-COLOR)
    (any . ,ANYTHING-COLOR)))
(define (type->color ty) (cdr (assv ty TYPE-COLOR-LIST)))

(define OP-LIST
  '((add1 number number)
    (sub1 number number)
    (zero? boolean number)
    (null? boolean any)
    (cons? boolean any)
    (car any list)
    (cdr any list)
    (cons list any any)
    (< boolean number number)
    (<= boolean number number)
    (> boolean number number)
    (>= boolean number number)
    (and boolean boolean)
    (or boolean boolean)
    (+ number number)
    (* number number)
    ;; program annotation
    (gray any any)
    (in any any)))


(define (default-op-fn color)
  (λ (size) (draw-polygon 4 size color)))

(define (GRAYOUT size)
  (just-image (draw-const size TRANSLUCENT-GRAY)))

(define OP-FN-LIST
  (list
   (cons 'add1 (default-op-fn NUMBER-COLOR))
   (cons 'sub1 (default-op-fn NUMBER-COLOR))
   (cons 'zero? (default-op-fn BOOLEAN-COLOR))
   (cons 'null? (default-op-fn BOOLEAN-COLOR))
   (cons 'cons? (default-op-fn BOOLEAN-COLOR))
   (cons 'car (default-op-fn ANYTHING-COLOR))
   (cons 'cdr (default-op-fn ANYTHING-COLOR))   
   (cons 'cons (default-op-fn LIST-COLOR))
   (cons '<  (default-op-fn BOOLEAN-COLOR))
   (cons '<= (default-op-fn BOOLEAN-COLOR))
   (cons '> (default-op-fn BOOLEAN-COLOR))
   (cons '>= (default-op-fn BOOLEAN-COLOR))
   (cons 'and (default-op-fn BOOLEAN-COLOR))
   (cons 'or (default-op-fn BOOLEAN-COLOR))
   (cons '+ (default-op-fn NUMBER-COLOR))
   (cons '* (default-op-fn NUMBER-COLOR))
   (cons 'if (λ (ty) (default-op-fn (type->color ty))))
   (cons 'λ (λ (k) (λ (size) (draw-polygon (max 4 k) size FUNCTION-COLOR))))
   (cons 'app (λ (k) (λ (size) (draw-polygon (max 4 k) size FUNCTION-COLOR))))
   (cons 'in (default-op-fn "white"))
   (cons 'let (default-op-fn "white"))
   (cons 'gray GRAYOUT)))

(define (op->type op) (cadr (assv op OP-LIST)))
(define (op->argtys op) (cddr (assv op OP-LIST)))
(define (op->wrapper-fn op)
  (cdr (assv op OP-FN-LIST)))

;; numeric constants
(define IMAGE-SIZE 1000)
(define CENTER (/ IMAGE-SIZE 2))
(define MIN-SIZE 1)
(define POLYGON-ANGLE -50)
(define POLYGON-%-PARAM .2)
(define PULLED-SQUARE-SIZE .55)
(define PULLED-POLYGON-SIZE .44)

(define SUBIMG-SIZE .8)
(define UNARY-SUBIMG-SIZE .9)
(define λ-SUBIMG-SIZE .9)
;; image building

(define (square? img size)
  (let ((x (image-width img))
        (y (image-height img)))
    (and (equal? x y) (equal? x size))))


;; drawing pulled regular polygons (for now, the only shape used to group subimages together)

(define (subimg-max size)
  (* size SUBIMG-SIZE))
(define (unary-subimg-max size)
  (* size UNARY-SUBIMG-SIZE))

(define ((poly-subimg-max k) size)
  (let* ((k (if (<= k 4) 4 k))
         (r (exact-floor (* size (if (= k 4) PULLED-SQUARE-SIZE PULLED-POLYGON-SIZE))))
         (int-angle (* 180 (- k 2) (/ 1 k)))
         (apothem (* r (sin (degrees->radians (/ int-angle 2))))))
    (* (if (= k 4) 1 λ-SUBIMG-SIZE) 2 apothem)))

(define (do-polygon mode k size color)
  (let* ((r (exact-floor (* size (if (= k 4) PULLED-SQUARE-SIZE PULLED-POLYGON-SIZE))))
         (int-angle (* 180 (- k 2) (/ 1 k)))
         (side-length (* 2 r (cos (degrees->radians (/ int-angle 2))))))
    (overlay 
     (pulled-regular-polygon side-length k POLYGON-%-PARAM POLYGON-ANGLE mode color)
     (square size "solid" TRANSPARENT))))

(define (draw-polygon k size color)
  (do-polygon "outline" k size color))

(define (draw-const size color)
  (let ((c (/ size 2)))
    (values (do-polygon "solid" 4 size color) (cons c c) size)))

;; math relating to finding image centers/ significant images
(define (calculate-center i row-size ds k-init size addy)
  (let loop ((ds ds)
             (x k-init)
             (y k-init)
             (i i)
             (size-left size))
    (cond
      ((null? ds) (begin (displayln "shouldnt get here") (values (cons x y) 0)))
      ((zero? i) (let* ((c (car ds))
                        (c2 (/ c 2)))
                   (values
                    (cons (+ (/ (- size (* row-size c)) 2) x c2)
                          (+ addy y c2))
                    c)))
      ((>= i row-size) (loop (drop ds row-size) x (+ y (car ds)) (- i row-size) (- size-left (car ds))))
      (else (loop (cdr ds) (+ x (car ds)) y (sub1 i) size-left)))))

(define (find-largest-depth es)
  (let loop ((dmax 0)
             (j 0)
             (i 0)
             (es es))
    (cond
      ((null? es) j)
      (else (let ((d (depth (car es))))
              (if (> d dmax)
                  (loop d i (add1 i) (cdr es))
                  (loop dmax j (add1 i) (cdr es))))))))

(define (find-largest-depth/expr es)
  (let loop ((dmax 0)
             (e (car es))
             (i 0)
             (es es))
    (cond
      ((null? es) e)
      (else (let ((d (depth (car es))))
              (if (> d dmax)
                  (loop d (car es) (add1 i) (cdr es))
                  (loop dmax e (add1 i) (cdr es))))))))

(define (calculate-used/y k ls)
  (let ((ls (split k ls)))
    (foldr (λ (x a) (+ (car x) a)) 0 ls)))

;; assembling multiple images

(define (do-beside l) (foldr beside empty-image l))

(define (share-depths k ls)
  (let loop ((i k)
             (curr 0)
             (ls ls))
    (cond
      [(null? ls) (build-list (- k i) (λ (_) curr))]
      [(zero? i) (append (build-list k (λ (_) curr)) (loop k 0 ls))]
      [else (let ((d (caar ls)))
                  (loop (sub1 i) (max curr d) (cdr ls)))])))



(define (distribute-size-and-arrange size es tys i relative-upper-left)
  (let* ((k (length es))
         (row-size (exact-ceiling (sqrt k)))
         (kmax (sqr row-size))
         (es (append es (build-list (- kmax k) (λ (_) '(blank)))))
         (tys (append tys (build-list (- kmax k) (λ (_) 'any))))
         (es/ds (map (λ (e) (let ((d (depth e))) (cons d e))) es))
         (ds (share-depths row-size es/ds))
         (init-size (sqrt (/ (sqr size) kmax)))
         (avg-depth (/ (foldr + 0 ds) kmax))
         (go (λ (e d t)
               (just-image (draw-code (min (/ size row-size) (* init-size (/ d avg-depth))) e t #f))))
         (res (let loop ((imgs (map go es ds tys)))
                (cond
                  [(null? imgs) empty-image]
                  [(< (length imgs) row-size)
                   (begin (displayln "shouldnt get here")
                          (do-beside imgs))]
                  [else (above (do-beside (take imgs row-size))
                               (loop (drop imgs row-size)))])))
         (scaled-depths (map (λ (d) (min (/ size row-size) (* init-size (/ d avg-depth)))) ds))
         (size-used/y (/ (- size (calculate-used/y row-size scaled-depths)) 2)))
    (let-values (((c size) (calculate-center i row-size scaled-depths relative-upper-left size size-used/y)))
      (values res c size))))

;; helpers for each case
(define (draw-blank size) (draw-const size TRANSPARENT))
(define (draw-symbol size y color) (draw-const size color))
(define (draw-bool size b) (draw-const size BOOLEAN-COLOR))
(define (draw-number size k) (draw-const size NUMBER-COLOR))
(define (draw-null size) (draw-const size LIST-COLOR))

(define (calc-corner big small)
  (/ (- big small) 2))

(define (draw-subimgs f max-size-fn size es tys ty i)
  (let* ((subimg-size (max-size-fn size))
         (upper-left (calc-corner size subimg-size)))
    (let-values (((img cen size^) (distribute-size-and-arrange subimg-size es tys i 0)))
      (values (overlay (f size) img)
              (cons (+ upper-left (car cen))
                    (+ upper-left (cdr cen)))
              size^))))

(define (draw-unary sym subexp size ty)
  (draw-subimgs (op->wrapper-fn sym) unary-subimg-max size `(,subexp) (op->argtys sym) (op->type sym) 0))

(define (draw-arb-arity sym sls size d?)
  (let* ((aty (car (op->argtys sym)))
         (tys (build-list (length sls) (λ (_) aty))))
    (draw-subimgs (op->wrapper-fn sym) subimg-max size sls tys (op->type sym) (if d? (find-largest-depth sls) 0))))

(define (draw-binary sym se1 se2 size d?)
  (let ((ls (list se1 se2)))
    (draw-subimgs (op->wrapper-fn sym) subimg-max size ls (op->argtys sym) (op->type sym) (if d? (find-largest-depth ls) 0))))

(define (draw-if v t c a size ty)
  (let ((b (boolean? v)))
    (define (package-if)
      (if b (if v (list t c `(gray, a)) (list t `(gray ,c) a)) (list t c a)))
  (let ((i (if b (if v 1 2) (find-largest-depth (list t c a)))))
    (draw-subimgs ((op->wrapper-fn 'if) ty) subimg-max size (package-if) `(boolean ,ty ,ty) ty i))))

(define (draw-lambda k-args e size)
  (draw-subimgs ((op->wrapper-fn 'λ) k-args) (poly-subimg-max k-args) size `(,e) '(any) 'function 0))

(define (draw-app f vs k-args size ty)
  (draw-subimgs
   ((op->wrapper-fn 'app) k-args)
   (poly-subimg-max k-args)
   size (cons f vs)
   (cons 'function (build-list k-args (λ (_) 'any)))
   ty 0))

(define (draw-let ds b size ty)
  (draw-subimgs
   (op->wrapper-fn 'let)
   subimg-max
   size (cons `(in ,b) (map cadr ds))
   (cons ty (build-list (length ds) (λ (_) 'any)))
   ty 0))

;; Putting it all together

(define (draw/calc size C ty d?)
  (match C
    [(? boolean? b) (draw-bool size b)]
    [(? number? k) (draw-number size k)]
    ['empty (draw-null size)]
    [(? symbol? y) (draw-symbol size y (type->color ty))]
    ['(blank) (draw-blank size)]
    [`(with-depth ,(? unary-op? o) ,d ,e) (draw-unary o e size ty)]
    [`(with-depth ,(? binary-op? o) ,d ,e1 ,e2) (draw-binary o e1 e2 size d?)]
    [`(with-depth ,(? arb-op? o) ,d . ,es) (draw-arb-arity o es size d?)]
    [`(with-depth if ,d ,v ,t ,c ,a) (draw-if v t c a size ty)]
    [`(λ ,xs ,b) (draw-lambda (length xs) b size)]
    [`(with-depth app ,d ,res-exp . ,args) (draw-app res-exp args (length args) size ty)]
    ;; forms for code which won't be zoomed into (may occur in unused if branches and unapplied lambdas)
    [`(,(? unary-op? o) ,e) (draw-unary o e size ty)]
    [`(,(? binary-op? o) ,e1 ,e2) (draw-binary o e1 e2 size d?)]
    [`(,(? arb-op? o) . ,es) (draw-arb-arity o es size d?)]
    [`(if ,d ,t ,c ,a) (draw-if 'unsure t c a size ty)]
    [`(let ,ds ,b) (draw-let ds b size ty)]
    [`(,f . ,vs) (draw-app f vs (length vs) size ty)]))

(define (draw-code size C ty b)
  (if (< size MIN-SIZE)
      (let ((k (/ size 2)))
        (values empty-image (cons k k) MIN-SIZE))
      (draw/calc size C ty b)))

(define (draw-prog p)
  (let* ((p (run '() p))
         (k (depth p))
         (img-size IMAGE-SIZE))
    (overlay (just-image (draw-code img-size p 'any #t))
             (square img-size "solid" BACKGROUND-COLOR))))


(define SCALE-FACTOR 1.1)
(define SHIFT-DIST .2)
(define DIST-MIN 5)

(define (picture-ready? x y size)
  (or (> size IMAGE-SIZE)
      (and (<= (abs (- x CENTER)) DIST-MIN)
           (<= (abs (- y CENTER)) DIST-MIN)
           (<= (abs (- size IMAGE-SIZE)) DIST-MIN))))

(define (do-x img dist-x)
      (let ((border (abs (* dist-x SHIFT-DIST))))
        (if (> dist-x 0)
            (beside (rectangle border IMAGE-SIZE "solid" BACKGROUND-COLOR)
                    (crop 0 0 (- IMAGE-SIZE border) IMAGE-SIZE img))
            (beside (crop border 0 (- IMAGE-SIZE border) IMAGE-SIZE img)
                    (rectangle border IMAGE-SIZE "solid" BACKGROUND-COLOR)))))
    (define (do-y img dist-y)
      (let ((border (abs (* dist-y SHIFT-DIST))))
        (if (> dist-y 0)
            (above (rectangle IMAGE-SIZE border "solid" BACKGROUND-COLOR)
                   (crop 0 0 IMAGE-SIZE (- IMAGE-SIZE border) img))
            (above (crop 0 border IMAGE-SIZE (- IMAGE-SIZE border) img)
                   (rectangle IMAGE-SIZE border "solid" BACKGROUND-COLOR)))))

(define (step-img img x y size)
  (let ((dist-x (- CENTER x))
        (dist-y (- CENTER y))
        (border (/ (- (* IMAGE-SIZE SCALE-FACTOR) IMAGE-SIZE) 2)))
    (values
     (crop border border
           IMAGE-SIZE IMAGE-SIZE
           (scale SCALE-FACTOR (do-y (do-x img dist-x) dist-y)))
     (- (* SCALE-FACTOR (+ x (* dist-x SHIFT-DIST))) border)
     (- (* SCALE-FACTOR (+ y (* dist-y SHIFT-DIST))) border)
     (* size SCALE-FACTOR))))

(struct World
  (exp img curr-x curr-y curr-size ty))


(define (tick-handler W)
  (match W
    [(World e i x y size ty)
     (if (picture-ready? x y size)
         (if e
             (let*-values (((i center size) (draw-code IMAGE-SIZE e ty #t))
                           ((e ty) (subimg e ty))
                           ((i) (give-background i)))
               (World e i (car center) (cdr center) size ty))
             (World #f i CENTER CENTER IMAGE-SIZE ty))
         (let-values (((i x y size) (step-img i x y size)))
           (World e i x y size ty)))]))

(define CIRCLE (circle 2 "solid" "yellow"))
(define (give-background i)
  (overlay i (rectangle IMAGE-SIZE IMAGE-SIZE "solid" "black")))

(define (draw-world W)
  (match W
    [(World e i x y size ty)
     (if e
         #;i
         (place-image CIRCLE x y i)
         (text "done!" 100 "black"))]))

(require 2htdp/universe)

(define (print-depth W)
  (match W
    [(World e i x y size ty) (displayln (depth e))]))

(define (main e)
  (let ((e (run '() e)))
    (let-values (((i cent size) (draw-code IMAGE-SIZE e 'any #t))
                 ((e ty) (subimg e 'any)))
      (big-bang (World e (give-background i) (car cent) (cdr cent) size ty)
        [on-tick tick-handler]
        #;[on-key (λ (e i) (match i
                           ["p" (begin (print-depth e)
                                       (tick-handler e))]
                           [else (tick-handler e)]))]
        [to-draw draw-world]))))

;; TODOs:
;have the depth calculating optional (at lower depths),
;and have expand re-called incrementally