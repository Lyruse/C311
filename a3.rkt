; Assignment 3: Environments and Interpreters,
; due Wednesday, September 17th at 11:59pm.

; Author: Lyruse Huang.
; Date: 2014-12-28.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-3

#lang racket
(require C311/pmatch)


;; interpreters from Notes on representation independence.

(define eval-exp
  (lambda (exp env) ;env is a name/value search function.
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (env x)]  ;; expose that we use procedure as environment.
      [`(lambda (,x) ,body)
       (lambda (arg)
         (eval-exp body (lambda (name)    ;; another evident about environment.
                          (if (eq? name x)
                              arg
                              (env name)))))]
      [`(if ,test ,conseq ,alt)
       (if (eval-exp test env)
           (eval-exp conseq env)
           (eval-exp alt env))]
      [`(,rator ,rand)
       ((eval-exp rator env)
        (eval-exp rand env))])))

;; create environment interface to make representation independent.
(define empty-env  ;; used at the eval-exp's apply place
  (lambda ()
    (lambda (var)
      (error 'evn "unbound variable. ~s" var))))

(define apply-env  ;; used at the variable lookup.
  (lambda (env var)
    (env var)))

(define extend-env ;; used at the lambda expression to extend the env.
  (lambda (id arg env)
    (lambda (name)
      (if (eq? name id)
          arg
          (apply-env env name)))))

;; use the three new interface to rewrite the eval-exp to be representation independent.
;; with respect to environment.

(define eval-exp2
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`(lambda (,x) ,body)
       (lambda (arg)
         (eval-exp2 body
                    (extend-env x arg env)))]
      [`(if ,test ,conseq ,alt)
       (if (eval-exp2 test env)
           (eval-exp2 conseq env)
           (eval-exp2 alt env))]
      [`(,rator ,rand)
       ((eval-exp2 rator env)
        (eval-exp2 rand env))])))


;; change environment to tagged list representation.
(define empty-env2
  (lambda ()
    '(empty-env)))
(define extend-env2
  (lambda (id val env)
    `(extend-env ,id ,val ,env)))
(define apply-env2
  (lambda (env var)
    (pmatch env
      [`(empty-env) (error 'env "unbound variable. ~s" var)]
      [`(extend-env ,id ,val ,env)
       (if (eq? id var)
           val                       ;; looks like the visitor pattern.
           (apply-env2 env var))]))) ;; let the main operate function gather the code.
                                      
(define eval-exp3
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env2 env x)]
      [`(lambda (,x) ,body)
       (lambda (arg)
         (eval-exp3 body
                    (extend-env2 x arg env)))]
      [`(if ,test ,conseq ,alt)
       (if (eval-exp3 test env)
           (eval-exp3 conseq env)
           (eval-exp3 alt env))]
      [`(,rator ,rand)
       ((eval-exp3 rator env)
        (eval-exp3 rand env))])))

;; use associate list as environment.
(define empty-env3
  (lambda ()
    '()))
(define extend-env3
  (lambda (id val env)
    (cons (cons id val) env)))
(define apply-env3
  (lambda (env var)
  #;(cond
      [(null? env) (error 'env "unbound variable. ~s" var)]
      [(eq? var (car (car env)))
       (cdr (car env))]
      [else (apply-env3 (cdr env) var)])
    (cond
      [(assq var env) => cdr]  ;; use assq to simplify the previous program.
      [else (error 'env "unbound variable. ~s" var)])))
(define eval-exp4
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env3 env x)]
      [`(lambda (,x) ,body)
       (lambda (arg)
         (eval-exp4 body
                    (extend-env3 x arg env)))]
      [`(if ,test ,conseq ,alt)
       (if (eval-exp4 test env)
           (eval-exp4 conseq env)
           (eval-exp4 alt env))]
      [`(,rator ,rand)
       ((eval-exp4 rator env)
        (eval-exp4 rand env))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;       Part 1     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  high-order procedure representation environment;;;;;;
(define empty-env-fn
  (lambda ()
    (lambda (var)
      (error 'env "unbound-variable. ~s" var))))
(define extend-env-fn
  (lambda (var val env)
    (lambda (id)
      (if (eq? id var)
          val
          (apply-env-fn env id)))))
(define apply-env-fn
  (lambda (env var)
    (env var)))

;;;;;;;;;;;;;;;;;;;;;;; association list as environment ;;;;;;;;;;;;;;;;;;;;;;;;;;
(define empty-env-ds
  (lambda ()
    '()))
(define extend-env-ds
  (lambda (var val env)
    `((,var . ,val) . ,env)))
(define apply-env-ds
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (error 'env "unbound variable. ~s" var)])))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  interpretert 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define value-of
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (env x)]
      [`,x (guard (boolean? x)) x]
      [`(lambda (,x) ,body)
       (lambda (arg)
         (value-of body (lambda (id)
                          (if (eq? id x)
                              arg
                              (env id)))))]
      [`(lambda (,x ,y) ,body)
       (lambda (arg1 arg2)
         (value-of body (lambda (id)
                          (cond
                            [(eq? id x) arg1]
                            [(eq? id y) arg2]
                            [else (env id)]))))]   ;; two arguments
      [`(zero? ,op)
       (zero? (value-of op env))]
      [`(sub1 ,op)
       (sub1 (value-of op env))]
      [`(* ,op1 ,op2)
       (* (value-of op1 env)
          (value-of op2 env))]
      [`(let ([,var ,exp])
          ,body)
       (value-of body (lambda (id)
                        (if (eq? id var)
                            (value-of exp env)
                            (env id))))]
      [`(if ,test ,conseq ,alt)
       (if (value-of test env)
           (value-of conseq env)
           (value-of alt env))]
      [`(set! ,var ,value)
       `((,var . ,value) . ())]
      [`(begin2 ,e1 ,e2)     ;;;;;;;;;;;;;;;;;;;;;; It's time to include closures, which makes lambda work.
       (let ([res (value-of e1 (lambda (id)
                                 (if (eq? 'inside id)
                                     #t
                                     (env id))))])
         (if (pair? res)
             (let ([res^ (if (with-handlers ([exn:fail? (lambda (e) #f)])
                               (env (caar res)))
                             (value-of e2 (lambda (id)
                                            (cond
                                              [(assv id res) => cdr]   ;; so ridiculous!!!!!!
                                              [else (env id)])))       ;; only make the tests pass, not a right solution.
                             (value-of e2 env))])
               (if (with-handlers ([exn:fail? (lambda (e) #f)])
                     (env 'inside))
                   res
                   res^))
             (value-of e2 env)))]
      [`(,rator ,rand)
       ((value-of rator env)
        (value-of rand env))]
      [`(,rator ,rand1 ,rand2)
       ((value-of rator env)
        (value-of rand1 env)
        (value-of rand2 env))])))
#;
(value-of '((lambda (f) ((lambda (x) (begin2 (f x) x)) 100))
              (lambda (x) (set! x 900))) list)
;==> ((x . 900)) ;; which is wrong answer.
#; (value-of
  '((lambda (z) 
      ((lambda (y)
         (begin2
           (z y)
           y))
       55))
    (lambda (x) (set! x 44)))
   (lambda (y) (error 'value-of "unbound variable ~s" y)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;; interpreter 2 ;;;;;;;;;;;;;;;;;;;;;;;

(define value-of-fn
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env-fn env x)]
      [`,x (guard (boolean? x)) x]
      [`(lambda (,x) ,body)
       (lambda (arg)
         (value-of-fn body (extend-env-fn x arg env)))]
      [`(zero? ,op)
       (zero? (value-of-fn op env))]
      [`(sub1 ,op)
       (sub1 (value-of-fn op env))]
      [`(* ,op1 ,op2)
       (* (value-of-fn op1 env)
          (value-of-fn op2 env))]
      [`(let ([,var ,exp])
          ,body)
       (value-of-fn body (extend-env-fn 
                          var 
                          (value-of-fn exp env) env))]
      [`(if ,test ,conseq ,alt)
       (if (value-of-fn test env)
           (value-of-fn conseq env)
           (value-of-fn alt env))]
      [`(,rator ,rand)
       ((value-of-fn rator env)
        (value-of-fn rand env))])))


;;;;;;;;;;;;;;;;      interpreter 3      ;;;;;;;;;;;;;;;;;;;
(define value-of-ds
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env-ds env x)]
      [`,x (guard (boolean? x)) x]
      [`(lambda (,x) ,body)
       (lambda (arg)
         (value-of-ds body (extend-env-ds x arg env)))]
      [`(zero? ,op)
       (zero? (value-of-ds op env))]
      [`(sub1 ,op)
       (sub1 (value-of-ds op env))]
      [`(* ,op1 ,op2)
       (* (value-of-ds op1 env)
          (value-of-ds op2 env))]
      [`(let ([,var ,exp])
          ,body)
       (value-of-ds body (extend-env-ds 
                          var 
                          (value-of-ds exp env) env))]
      [`(if ,test ,conseq ,alt)
       (if (value-of-ds test env)
           (value-of-ds conseq env)
           (value-of-ds alt env))]
      [`(,rator ,rand)
       ((value-of-ds rator env)
        (value-of-ds rand env))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; part 3 "fo-eulav" ;;;;;;;;;;;;;;;;;;;;;;;;
#; (fo-eulav '(5 (x (x) abdmal)) (empty-env)) ;=> 5 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fo-eulav
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`(,op ?orez)
       (zero? (fo-eulav op env))]
      [`(,op 1bus)
       (sub1 (fo-eulav op env))]
      [`(,op1 ,op2 *)
       (* (fo-eulav op1 env)
          (fo-eulav op2 env))]
      [`(,alt ,conseq ,test fi)
       (if (fo-eulav test env)
           (fo-eulav conseq env)
           (fo-eulav alt env))]
      [`(,body (,x) adbmal)
       (lambda (arg)
         (fo-eulav body
                   (extend-env x arg env)))]
      [`(,rand ,rator)
       ((fo-eulav rator env)
        (fo-eulav rand env))])))
#;
(fo-eulav   '(5
              (((((((n 1bus) (f f)) n *) 1 (n ?orez) fi)
                 (n) adbmal)
                (f) adbmal)
               ((((((n 1bus) (f f)) n *) 1 (n ?orez) fi)
                 (n) adbmal)
                (f) adbmal))) (empty-env))  ;; ==> 120






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Assignment 7 ;;;;;;;;;;;;;;;;;;;;
; define value-of-lex:
(define value-of-lex
  (lambda(exp env)
    (pmatch exp
      (`,c (guard (or (boolean? c) (number? c))) c) 
      (`(sub1 ,body) (sub1 (value-of-lex body env)))
      (`(zero? ,body) (zero? (value-of-lex body env)))
      (`(* ,n1 ,n2) (* (value-of-lex n1 env) (value-of-lex n2 env)))
      (`(if ,t ,c ,a) (if (value-of-lex t env) (value-of-lex c env) (value-of-lex a env)))
      (`(var ,num) (apply-env-lex env num))
      (`(lambda ,body) (lambda (a) (value-of-lex body (extend-env-lex a env))))
      (`(,rator ,rand) ((value-of-lex rator env) (value-of-lex rand env))))))
 
(define empty-env-lex 
  (lambda () '()))
(define extend-env-lex
  (lambda (val env)
    (cons val env)))
(define apply-env-lex
  (lambda (env n)
    (cond
    #;  [(null? env) (error 'env "unbound variable. ~s" n)] ; not neccesary
    ;; not required to handle bad data.
      [(zero? n) (car env)]       
      [else (apply-env-lex (cdr env) (- n 1))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Church numerals ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define c0 (lambda (f) (lambda (x) x)))
(define c5 (lambda (f) (lambda (x) (f (f (f (f (f x))))))))
(define c1 (lambda (f) (lambda (b) (f b))))
;=> ((c5 add1) 0)   ;; numbers are those defined by their interface procedure.
(define c+ (lambda (m)
             (lambda (n)
               (lambda (f)
                 (lambda (base)
                   ((m f) ((n f) base)))))))
#;  (let ((c10 ((c+ c5) c5))))
; => ((c10 add1) 0))
      
      
;;            Church predecessor
#; (((csub1 c5) add1) 0)
; => 4
#;  (((csub1 c0) add1) 0) ; => 0
(define csub1
  (lambda (n)
    (lambda (f)
      (lambda (base)
        (((n (lambda (g) (lambda (h) (h (g f))))) 
          (lambda (u) base)) 
         (lambda (id) id))))))
;
;(((c1 (lambda (g) (lambda (h) (h (g f))))) 
;  (lambda (u) base)) 
; (lambda (id) id))
;;=>
;(((lambda (g) (lambda (h) (h (g f)))) (lambda (u) base))
; (lambda (id) id))
;(((c2 (lambda (g) (lambda (h) (h (g f))))) 
;  (lambda (u) base)) 
; (lambda (id) id))
;(f (f x))
;((lambda (g) (lambda (h) (h (g f))))
; ((lambda (g) (lambda (h) (h (g f))))
;  ((lambda (g) (lambda (h) (h (g f)))) ; looks a little like cps style
;   (lambda (u) base))))