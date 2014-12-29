; Assignment 5: Parameter-Passing Conventions

; Author: Lyruse Huang.
; Date: 2014-12-29.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-5

#lang racket
(require C311/pmatch)
(require math/number-theory)
#;(require C311/a5-student-tests)
#;(test-file)
;; test result: 
;; 16 success(es) 0 failure(s) 0 error(s) 16 test(s) run. Perfect.

;;;;;;;;;;;;;;;;;;;;;;; association list as environment ;;;;;;;;;;;;;;;;;;;;;;;;;;
(define empty-env
  (lambda ()
    '()))
(define extend-env
  (lambda (var val env)
    `((,var . ,val) . ,env)))
(define apply-env
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (error 'env "unbound variable. ~s" var)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;closure representation using data-structure;;;;;;;;;;;;;;;
(define closure
  (lambda (x body env)
    `(closure ,x ,body ,env)))
(define apply-closure
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (value-of body (extend-env x arg env))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define value-of
  (lambda (exp env)
    (pmatch exp
      [`,b (guard (boolean? b)) b]
      [`,n (guard (number? n)) n]
      [`(zero? ,n) (zero? (value-of n env))]
      [`(sub1 ,n) (sub1 (value-of n env))]
      [`(* ,n1 ,n2) (* (value-of n1 env) (value-of n2 env))]
      [`(if ,test ,conseq ,alt) (if (value-of test env)
                                    (value-of conseq env)
                                    (value-of alt env))]
      [`(begin2 ,e1 ,e2) (begin (value-of e1 env) (value-of e2 env))]
      [`(random ,n) (random (value-of n env))]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`(lambda (,x) ,body) (closure x body env)]
      [`(,rator ,rand) (apply-closure (value-of rator env)
                                      (value-of rand env))])))


#|
Convention	     Interpreter Name
call-by-value	val-of-cbv
call-by-reference	val-of-cbr
call-by-name	val-of-cbname
call-by-need	val-of-cbneed
|#

;;;;;;;;;;;;;;;;   interpreter for Call-by-value   ;;;;;;;;;;;;;;;;;;;
; environment utilities
(define empty-env-cbv   ;; same as empty-env, which will be used in tests.
  (lambda ()
    '()))
(define extend-env-cbv
  (lambda (var val env)
    `((,var . ,(box val)) . ,env)))  ;; use box to implement set! syntax.
(define apply-env-cbv
  (lambda (env var)
    (cond
      [(assq var env) => (lambda (p) (unbox (cdr p)))]
      [else (error 'env "unbound variable. ~s" var)])))
(define apply-env-cbv-set!  
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (error 'env "unbound variable. ~s" var)])))

; closure representation 
(define closure-cbv
  (lambda (x body env)
    `(closure ,x ,body ,env)))
(define apply-closure-cbv       
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (val-of-cbv body (extend-env-cbv x arg env))])))
; ==================utility for lazy cons ======================
(define unbox/cons
  (lambda (b)
    (let ([res ((unbox b))])
      (set-box! b (lambda () res))
      res)))


(define val-of-cbv
  (lambda (exp env)
    (pmatch exp
      [`,b (guard (boolean? b)) b]
      [`,n (guard (number? n)) n]
      [`,x (guard (symbol? x)) (apply-env-cbv env x)]
      [`(quote ()) '()]
      [`(null? ,ls) (null? (val-of-cbv ls env))]
      [`(zero? ,n) (zero? (val-of-cbv n env))]
      [`(add1 ,n) (add1 (val-of-cbv n env))]
      [`(sub1 ,n) (sub1 (val-of-cbv n env))]
      [`(* ,n1 ,n2) (* (val-of-cbv n1 env) (val-of-cbv n2 env))]
      [`(if ,test ,conseq ,alt) (if (val-of-cbv test env)
                                    (val-of-cbv conseq env)
                                    (val-of-cbv alt env))]
      [`(begin2 ,e1 ,e2) (begin (val-of-cbv e1 env) (val-of-cbv e2 env))]
      [`(let ([,x ,e])
          ,body)
       (val-of-cbv body (extend-env-cbv x (val-of-cbv e env) env))]
      [`(cons^ ,a ,d)  ;; lazy version of cons
       (cons (box (lambda () (val-of-cbv a env)))
             (box (lambda () (val-of-cbv d env))))]
      [`(car^ ,ls)
       (unbox/cons (car (val-of-cbv ls env)))]
      [`(cdr^ ,ls)
       (unbox/cons (cdr (val-of-cbv ls env)))]
      [`(cons ,a ,d)  ;; strict version
       (cons (val-of-cbv a env) (val-of-cbv d env))]
      [`(car ,ls)
       (car (val-of-cbv ls env))]
      [`(cdr ,ls)
       (car (val-of-cbv ls env))]
      [`(set! ,var ,rhs)
       (let ([val (val-of-cbv rhs env)]
             [var (apply-env-cbv-set! env var)])
         (set-box! var val))]
      [`(random ,n) (random (val-of-cbv n env))]
      [`(lambda (,x) ,body) (closure-cbv x body env)]
      [`(,rator ,rand) (apply-closure-cbv
                        (val-of-cbv rator env)
                        (val-of-cbv rand env))])))




;;;;;;;;;;;;;;;;   interpreter for Call-by-reference   ;;;;;;;;;;;;;;;;;;;
; environment utilities
(define empty-env-cbr   ;; same as empty-env, which will be used in tests.
  (lambda ()
    '()))
(define extend-env-cbr
  (lambda (var val env) ; change at the apply position.
    (if (or (box? val) #;(list? val))   ;; make the input of closure also work, but it will not work when 
        `((,var . ,val) . ,env)       ;; support list . the better idea is to make it a unique object.
        `((,var . ,(box val)) . ,env))))  ;; use box to implement set! syntax.
(define apply-env-cbr
  (lambda (env var)
    (cond
      [(assq var env) => (lambda (p) (unbox (cdr p)))]
      [else (error 'env "unbound variable. ~s" var)])))
(define apply-env-cbr-box  ;; no longer need in this cbr
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (error 'env "unbound variable. ~s" var)])))

; closure representation 
(define closure-cbr
  (lambda (x body env)
    `(closure ,x ,body ,env)))
#;
(define apply-closure-cbr       
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (val-of-cbr body (extend-env-cbr x arg env))])))
(define apply-closure-cbr-im       
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (val-of-cbr-im body (extend-env-cbr x arg env))])))


; First Edition, pass the test from a5-student-test3.rkt, but not mine.
#;
(define val-of-cbr
  (lambda (exp env)
    (pmatch exp
      [`,b (guard (boolean? b)) b]
      [`,n (guard (number? n)) n]
      [`,x (guard (symbol? x)) (apply-env-cbr env x)]
      [`(zero? ,n) (zero? (val-of-cbr n env))]
      [`(sub1 ,n) (sub1 (val-of-cbr n env))]
      [`(* ,n1 ,n2) (* (val-of-cbr n1 env) (val-of-cbr n2 env))]
      [`(if ,test ,conseq ,alt) (if (val-of-cbr test env)
                                    (val-of-cbr conseq env)
                                    (val-of-cbr alt env))]
      [`(begin2 ,e1 ,e2) (begin (val-of-cbr e1 env) (val-of-cbr e2 env))]
      [`(set! ,var ,rhs)
       (let ([val (val-of-cbr rhs env)]
             [var (apply-env-cbr-box env var)])
         (set-box! var val))]
      [`(random ,n) (random (val-of-cbr n env))]
      [`(lambda (,x) ,body) (closure-cbr x body env)]
;      [`(,rator ,x) (guard (symbol? x))
;                    (apply-closure-cbr
;                     (val-of-cbr rator env)
;                     (apply-env-cbr-box env x))]  ; no longer need this clause.
      [`(,rator ,rand) (apply-closure-cbr
                        (val-of-cbr rator env)
                        (val-of-cbr rand env))])))
#;
 (val-of-cbr '((lambda (x)
                  (begin2 
                    ((lambda (y) (set! y 10000)) (if #t x 10))
                    x)) 
                99)
              (empty-env))
; this edition gives 99, but the real call by reference should return 10000

;; second edition, which makes every return value a box, aka a reference,
;; only unbox when it's neccesarry.
(define unpack (lambda (v)
                 (if (box? v)
                     (unbox v)
                     v)))
;; this edition pass the test above which first edition fails with.
(define val-of-cbr-im
  (lambda (exp env)
    (pmatch exp
      [`,b (guard (boolean? b)) b]
      [`,n (guard (number? n)) n]
      [`,x (guard (symbol? x)) (apply-env-cbr-box env x)]
      [`(zero? ,n) 
       (zero? (unpack (val-of-cbr-im n env)))]
      [`(sub1 ,n) (sub1 (unpack (val-of-cbr-im n env)))]
      [`(* ,n1 ,n2) (* (unpack (val-of-cbr-im n1 env)) (unpack (val-of-cbr-im n2 env)))]
      [`(if ,test ,conseq ,alt) (if (unpack (val-of-cbr-im test env))
                                    (val-of-cbr-im conseq env)
                                    (val-of-cbr-im alt env))]
      [`(begin2 ,e1 ,e2) (begin (val-of-cbr-im e1 env) (val-of-cbr-im e2 env))]
      [`(set! ,var ,rhs)
       (let ([val (unpack (val-of-cbr-im rhs env))]
             [var (apply-env-cbr-box env var)])
         (set-box! var val))]
      [`(random ,n) (random (unpack (val-of-cbr-im n env)))]
      [`(lambda (,x) ,body) (closure-cbr x body env)]
      [`(,rator ,x) (guard (symbol? x))
                    (apply-closure-cbr-im
                     (unpack (val-of-cbr-im rator env))
                     (apply-env-cbr-box env x))]
      [`(,rator ,rand) (apply-closure-cbr-im
                        (unpack (val-of-cbr-im rator env))
                        (val-of-cbr-im rand env))])))
(define val-of-cbr (lambda (exp env) (unpack (val-of-cbr-im exp env))))


;;;;;;;;;;;;;;;;;;;;;;    interpreter 3 call by name       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;closure representation using data-structure;;;;;;;;;;;;;;;
(define closure-cbname
  (lambda (x body env)
    `(closure ,x ,body ,env)))
(define apply-closure-cbname
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (val-of-cbname body (extend-env x arg env))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define val-of-cbname
  (lambda (exp env)
    (pmatch exp
      [`,b (guard (boolean? b)) b]
      [`,n (guard (number? n)) n]
      [`,x (guard (symbol? x)) ((unbox (apply-env env x)))]   ;; much easier writing unbox here
      [`(zero? ,n) (zero? (val-of-cbname n env))]           ;; instead writing in the env helper.
      [`(sub1 ,n) (sub1 (val-of-cbname n env))]
      [`(* ,n1 ,n2) (* (val-of-cbname n1 env) (val-of-cbname n2 env))]
      [`(if ,test ,conseq ,alt) (if (val-of-cbname test env)
                                    (val-of-cbname conseq env)
                                    (val-of-cbname alt env))]
      [`(begin2 ,e1 ,e2) (begin (val-of-cbname e1 env) (val-of-cbname e2 env))]
      [`(random ,n) (random (val-of-cbname n env))]
      [`(lambda (,x) ,body) (closure-cbname x body env)]
      [`(,rator ,rand) (apply-closure-cbname
                        (val-of-cbname rator env)
                        (box (lambda () (val-of-cbname rand env))))])))





;; ===================================================================================
;;;;;;;;;;;;;;;;;;;;;;;;;;;; interpreter 4 call by neeed ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;closure representation using data-structure;;;;;;;;;;;;;;;
(define closure-cbneed
  (lambda (x body env)
    `(closure ,x ,body ,env)))
(define apply-closure-cbneed
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (val-of-cbneed body (extend-env x arg env))])))
; ================ utility for evaluation and storage =====================
(define unbox/need
  (lambda (b)
    (let ([res ((unbox b))])
      (set-box! b (lambda () res))
      res)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define val-of-cbneed
  (lambda (exp env)
    (pmatch exp
      [`,b (guard (boolean? b)) b]
      [`,n (guard (number? n)) n]
      [`,x (guard (symbol? x)) (unbox/need (apply-env env x))]   ;; much easier writing unbox here
      [`(zero? ,n) (zero? (val-of-cbneed n env))]           ;; instead writing in the env helper.
      [`(sub1 ,n) (sub1 (val-of-cbneed n env))]
      [`(* ,n1 ,n2) (* (val-of-cbneed n1 env) (val-of-cbneed n2 env))]
      [`(if ,test ,conseq ,alt) (if (val-of-cbneed test env)
                                    (val-of-cbneed conseq env)
                                    (val-of-cbneed alt env))]
      [`(begin2 ,e1 ,e2) (begin (val-of-cbneed e1 env) (val-of-cbneed e2 env))]
      [`(random ,n) (random (val-of-cbneed n env))]
      [`(lambda (,x) ,body) (closure-cbneed x body env)]
      [`(,rator ,rand) (apply-closure-cbneed
                        (val-of-cbneed rator env)
                        (box (lambda () (val-of-cbneed rand env))))])))