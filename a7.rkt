; Assignment 7: Continuations and Representation Independence

; Author: Lyruse Huang.
; Date: 2014-12-31.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-7

#lang racket
(require C311/pmatch)
#;(require C311/a7-student-tests)
#;(test-file)
; test result:
; 7 success(es) 0 failure(s) 0 error(s) 7 test(s) run. Still perfect.

(define empty-k
  (lambda ()
    (let ([once-only #f])
      (lambda (v)
        (if once-only
            (error 'empty-k "You can only invoke the emtpy continuation once.")
            (begin (set! once-only #t) v))))))
;;========================= A 1 ==================================
(define binary-to-decimal
  (lambda (n)
    (cond
      [(null? n) 0]
      [else (+ (car n) (* 2 (binary-to-decimal (cdr n))))])))
(define binary-to-decimal-cps
  (lambda (n k)
    (cond
      [(null? n) (k 0)]
      [else (binary-to-decimal-cps (cdr n)
                                   (lambda (r)
                                     (k (+ (car n) (* 2 r)))))])))
#; (binary-to-decimal-cps '(0 0 0 0 0 0 0 0 0  0 1) (empty-k))
; => 1024
; ========================== A 2 ====================================
(define rember*?
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [(pair? (car ls))
       (cond
         [(equal? (car ls) (rember*? (car ls)))
          (cons (car ls) (rember*? (cdr ls)))]
         [else (cons (rember*? (car ls)) (rember*? (cdr ls)))])]
      [(eqv? (car ls) '?) (rember*? (cdr ls))]
      [else (cons (car ls) (rember*? (cdr ls)))])))
(define rember*?-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k '())]
      [(pair? (car ls))
       (rember*?-cps (car ls)
                     (lambda (a)
                       (cond
                         [(equal? (car ls) a)
                          (rember*?-cps (cdr ls)
                                        (lambda (d)
                                          (cons (car ls) d)))]
                         [else (rember*?-cps (cdr ls)
                                             (lambda (d)
                                               (k (cons a d))))])))]
      [(eqv? (car ls) '?) (rember*?-cps (cdr ls) k)]
      [else (rember*?-cps (cdr ls)
                          (lambda (d)
                            (k (cons (car ls) d))))])))
#;(rember*?-cps '(1 23 (? 352 1 d (hello ? world)(?)a)) (empty-k))
; => (1 23 (352 1 d (hello world) () a))


; ======================    Part 2    ====================================
;;;;;;;;;;;;;;;;;;;;; Environment using data structure ;;;;;;;;;;;;;;;;;;;
(define empty-env
  (lambda ()
    '()))
(define extend-env
  (lambda (x v env)
    `((,x . ,v) . ,env)))
(define apply-env
  (lambda (env x)
    (cond
      [(assq x env) => cdr]
      [else (error 'env "unbound variable: ~s." x)])))
;;;;;;;;;;;;;;;;;;;;;;;; Closure using data structure ;;;;;;;;;;;;;;;;;;;;;;
(define closure
  (case-lambda 
    [(x body env)
     `(closure ,x ,body ,env)]
    [(x1 x2 body env)
     `(closure ,x1 ,x2 ,body ,env)]))

(define apply-closure-cps
  (case-lambda 
    [(rator rand ctx)
     (pmatch rator
       [`(closure ,x ,body ,env)
        (value-of-cps body (extend-env x rand env) ctx)])]
    [(rator rand1 rand2 ctx)
     (pmatch rator
       [`(closure ,x1 ,x2 ,body ,env)
        (value-of-cps body (extend-env x2 rand2 (extend-env x1 rand1 env)) ctx)])]))
#|

(define apply-closure-cps-ds
  (lambda (rator rand)
    (pmatch rator
      [`(closure ,x ,body ,env)
       (value-of-cps-ds body (extend-env x rand env))])))
|#

;Description	                                            Name
;CPSed interpreter 	                                  value-of-cps
;CPSed interpreter uses functional continuation helpers	  value-of-cps-fn
;CPSed interpreter uses data-structural continuation helpers value-of-cps-ds
; only cost me few minutes to finish thie interpreter. So Great.
(define value-of-cps
  (lambda (expr env ctx)
    (pmatch expr
      [`,n (guard (or (number? n) (boolean? n))) (ctx n)]
      [`(+ ,x1 ,x2)
       (value-of-cps x1 env
                     (lambda (x1)
                       (value-of-cps x2 env
                                     (lambda (x2)
                                       (ctx (+ x1 x2))))))]
      [`(* ,x1 ,x2) 
       (value-of-cps x1 env (lambda (x1)
                              (value-of-cps x2 env
                                            (lambda (x2)
                                              (ctx (* x1 x2))))))]
      [`(sub1 ,x) 
       (value-of-cps x env (lambda (x)
                             (ctx (sub1 x))))]
      [`(zero? ,x) (value-of-cps x env (lambda (x)
                                         (ctx (zero? x))))]
      [`(if ,test ,conseq ,alt) 
       (value-of-cps test env (lambda (t)
                                (if t
                                    (value-of-cps conseq env ctx)
                                    (value-of-cps alt env ctx))))]
      [`(capture ,k-id ,body)
       (value-of-cps body (extend-env k-id ctx env) ctx)]
      [`(return ,v-exp ,k-exp) 
       (value-of-cps k-exp env
                     (lambda (k)
                       (value-of-cps v-exp env k)))]
      [`,x (guard (symbol? x)) (ctx (apply-env env x))]
      [`(lambda (,id) ,body) (ctx (closure id body env))]
      [`(lambda (,id1 ,id2) ,body) (ctx (closure id1 id2 body env))]
      [`(,rator ,rand) 
       (value-of-cps rator env 
                     (lambda (rator)
                       (value-of-cps rand env
                                     (lambda (rand)
                                       (apply-closure-cps
                                        rator
                                        rand
                                        ctx)))))]
      [`(,rator ,rand1 ,rand2)
       (value-of-cps rator env 
                     (lambda (rator)
                       (value-of-cps rand1 env
                                     (lambda (rand1)
                                       (value-of-cps rand2 env
                                                     (lambda (rand2)
                                                       (apply-closure-cps
                                                        rator
                                                        rand1
                                                        rand2
                                                        ctx)))))))])))
#;#;#;#;#;
(define fact-5
  '((lambda (f)
      ((f f) 5))
    (lambda (f)
      (lambda (n)
        (if (zero? n)
            1
            (* n ((f f) (sub1 n))))))))
(define capture-fun
  '(* 3 (capture q (* 2 (return 4 q)))))
(value-of-cps fact-5 (empty-env) (empty-k)) ; => 120
(value-of-cps capture-fun (empty-env) (empty-k)) ;=> 12   ; they all work!!
(define fact-5-cps
  '((lambda (f k)
      (f f (lambda (f) (f 5 k))))
    (lambda (f k)
      (k (lambda (n k)
           (if (zero? n)
               (k 1)
               (f f (lambda (f)
                      (f (sub1 n) (lambda (r)
                                    (k (* n r))))))))))
    (lambda (id) id)))
#;(value-of-cps fact-5-cps (empty-env) (empty-k)) 
; can't work for the interpreter can't handle more than one argument 
; in the application form. Try to expand it.
; 2014-12-31 4:29am after about several minutes's work, I made it!
;=> 120      So glad to gain the power that I couldn't imagine.


;=====================================================================================
;=====================================================================================
;============================== value-of-cps-fn ======================================
(define empty-k-fn empty-k)
(define apply-closure-cps-fn
  (lambda (rator rand)
    (pmatch rator
      [`(closure ,x ,body ,env)
       (value-of-cps-fn body (extend-env x rand env))])))
(define context-tail-fn
  (lambda (f ctx)
    (lambda (x)
      (ctx (f x)))))
(define context-op-fn
  (lambda (x2 env * ctx)
    (lambda (x1)
      (value-of-cps-fn x2 env
                       (lambda (x2)
                         (ctx (* x1 x2)))))))
(define context-if-fn
  (lambda (conseq alt env ctx)
    (lambda (t)
      (if t
          (value-of-cps-fn conseq env ctx)
          (value-of-cps-fn alt env ctx)))))
(define context-return-fn  ;;; only for call/cc application.
  (lambda (v-exp env)
    (lambda (k)
      (value-of-cps-fn v-exp env k))))
(define context-app-fn     ;; for application.
  (lambda (rand apply-closure-cps env ctx)
    (lambda (rator)
      (value-of-cps-fn rand env
                       (lambda (rand)
                         (apply-closure-cps
                          rator
                          rand
                          ctx))))))

(define value-of-cps-fn
  (lambda (expr env ctx)
    (pmatch expr
      [`,n (guard (or (number? n) (boolean? n))) (ctx n)]
      [`(+ ,x1 ,x2)
       (value-of-cps-fn x1 env
                        (context-op-fn x2 env + ctx))]
      [`(* ,x1 ,x2) 
       (value-of-cps-fn x1 env (context-op-fn x2 env * ctx))]
      [`(sub1 ,x) 
       (value-of-cps-fn x env (context-tail-fn sub1 ctx))]
      [`(zero? ,x) (value-of-cps-fn x env (context-tail-fn zero? ctx))]
      [`(if ,test ,conseq ,alt) 
       (value-of-cps-fn test env (context-if-fn conseq alt env ctx))]
      [`(capture ,k-id ,body)
       (value-of-cps-fn body (extend-env k-id ctx env) ctx)]
      [`(return ,v-exp ,k-exp) 
       (value-of-cps-fn k-exp env
                        (context-return-fn v-exp env))] 
      [`,x (guard (symbol? x)) (ctx (apply-env env x))]
      [`(lambda (,id) ,body) (ctx (closure id body env))]
      [`(lambda (,id1 ,id2) ,body) (ctx (closure id1 id2 body env))]
      [`(,rator ,rand) 
       (value-of-cps-fn rator env 
                        (context-app-fn rand apply-closure-cps env ctx))])))



;=====================================================================================
;=====================================================================================
;============================== value-of-cps-ds ======================================
(define apply-closure-cps-ds
  (lambda (rator rand ctx)
    (pmatch rator
      [`(closure ,x ,body ,env)
       (value-of-cps-ds body (extend-env x rand env) ctx)])))

;====================continuation using data-structrue representation =================
(define empty-k-ds
  (lambda ()
    '(empty-k-ds)))
(define apply-context
  (lambda (ctx v)
    (pmatch ctx
      [`(empty-k-ds) v]
      [`(context-tail-ds ,f ,ctx)
       (apply-context ctx (f v))]
      [`(context-op-ds ,x2 ,env ,f ,ctx)
       (value-of-cps-ds x2 env (context-tail-f-ds v f ctx))]
      [`(context-tail-f-ds ,x1 ,f ,ctx)
       (apply-context ctx (f v x1))]
      [`(context-if-ds ,conseq ,alt ,env ,ctx)
       (if v
           (value-of-cps-ds conseq env ctx)
           (value-of-cps-ds alt env ctx))]
      [`(context-return-ds ,v-exp ,env)
       (value-of-cps-ds v-exp env v)]
      [`(context-app-ds ,rand ,env ,ctx)
       (value-of-cps-ds rand env (context-app-rand-ds v ctx))]
      [`(context-app-rand-ds ,rator ,ctx)
       (apply-closure-cps-ds rator v ctx)])))

(define context-tail-ds
  (lambda (f ctx)
    `(context-tail-ds ,f ,ctx)))

(define context-op-ds
  (lambda (x2 env f ctx)
    `(context-op-ds ,x2 ,env ,f ,ctx)))

(define context-tail-f-ds
  (lambda (v f ctx)
    `(context-tail-f-ds ,v ,f ,ctx)))

(define context-if-ds
  (lambda (conseq alt env ctx)
    `(context-if-ds ,conseq ,alt ,env ,ctx)))

(define context-return-ds  ;;; only for call/cc application.
  (lambda (v-exp env)
    `(context-return-ds ,v-exp ,env)))

(define context-app-ds
  (lambda (rand env ctx)
    `(context-app-ds ,rand ,env ,ctx)))

(define context-app-rand-ds
  (lambda (rator ctx)
    `(context-app-rand-ds ,rator ,ctx)))

;====================================================================================

(define value-of-cps-ds
  (lambda (expr env ctx)
    (pmatch expr
      [`,n (guard (or (number? n) (boolean? n))) 
           (apply-context ctx n)]
      [`(+ ,x1 ,x2)
       (value-of-cps-ds x1 env
                        (context-op-ds x2 env + ctx))]
      [`(* ,x1 ,x2) 
       (value-of-cps-ds x1 env (context-op-ds x2 env * ctx))]
      [`(sub1 ,x) 
       (value-of-cps-ds x env (context-tail-ds sub1 ctx))]
      [`(zero? ,x) 
       (value-of-cps-ds x env (context-tail-ds zero? ctx))]
      [`(if ,test ,conseq ,alt) 
       (value-of-cps-ds test env (context-if-ds conseq alt env ctx))]
      [`(capture ,k-id ,body)
       (value-of-cps-ds body (extend-env k-id ctx env) ctx)]
      [`(return ,v-exp ,k-exp) 
       (value-of-cps-ds k-exp env
                        (context-return-ds v-exp env))] 
      [`,x (guard (symbol? x))
           (apply-context ctx (apply-env env x))]
      [`(lambda (,id) ,body) 
       (apply-context ctx (closure id body env))]
#;    [`(lambda (,id1 ,id2) ,body) 
         (apply-context ctx (closure id1 id2 body env))]
      [`(,rator ,rand) 
       (value-of-cps-ds rator env 
                        (context-app-ds rand env ctx))])))
#;#;#;#;
(define fact-5
  '((lambda (f)
      ((f f) 5))
    (lambda (f)
      (lambda (n)
        (if (zero? n)
            1
            (* n ((f f) (sub1 n))))))))
(define capture-fun
  '(* 3 (capture q (* 2 (return 4 q)))))
(value-of-cps-ds fact-5 (empty-env) (empty-k-ds)) ; => 120
(value-of-cps-ds capture-fun (empty-env) (empty-k-ds)) ; =>12
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Braindteaser ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; implement streams, a data-structure that enables us to process infinite lists of items.
(define the-empty-stream '())
(define null?$ null?)
(define-syntax cons$
  (syntax-rules ()
    [(_ x y)
     (cons x (delay y))]))
(define car$ car)
(define cdr$
  (lambda ($) (force (cdr $))))
(define inf-1s (cons$ 1 inf-1s))
(define map$
  (lambda (proc $)
    (if (null?$ $)
        the-empty-stream
        (cons$ (proc (car$ $))
               (map$ proc (cdr$ $))))))
(define natural-numbers (cons$ 0 (map$ add1 natural-numbers)))
(define take$
  (lambda (n $)
    (cond
      [(zero? n) '()]
      [else (cons (car$ $) (take$ (sub1 n) (cdr$ $)))])))
#;(foldl + 0 (take$ 200 natural-numbers))
; => 19900

; implement the tribonacci stream which is a little like fibonacci, but
; the current number is the sum of the previous three number in the sequence.
(define zipWith$
  (lambda (f $1 $2)
    (cons$ (f (car$ $1)
              (car$ $2))
           (zipWith$ f
                     (cdr$ $1)
                     (cdr$ $2)))))
(define trib$
  (cons$ 0 
         (cons$ 1 
                (cons$ 1 
                       (zipWith$ +
                                 trib$
                                 (zipWith$ + 
                                           (cdr$ trib$)
                                           (cdr$ (cdr$ trib$))))))))
#;(take$ 10 trib$)
; => (0 1 1 2 4 7 13 24 44 81)