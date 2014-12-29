; Assignment 4: Dynamic Scope

; Author: Lyruse Huang.
; Date: 2014-12-29.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-4

#lang racket
(require C311/pmatch)
#;(require C311/a4-student-tests)
#;(test-file)
;; test result: 
;; 21 success(es) 0 failure(s) 0 error(s) 21 test(s) run.  Perfect!

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

;;;;;;;;;;;;;;;;;;;;;;;; closure representation using higher-order functions ;;;;;;;;;;;;;;
(define closure-fn
  (lambda (x body env)
    (lambda (arg)
         (value-of-fn body (extend-env x arg env)))))
(define apply-closure-fn
  (lambda (clo arg)
    (clo arg)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;closure representation using data-structure;;;;;;;;;;;;;;;
(define closure-ds
  (lambda (x body env)
    `(closure ,x ,body ,env)))
(define apply-closure-ds
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (value-of-ds body (extend-env x arg env))])))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;     interpreter 1    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define value-of-fn
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`,x (guard (boolean? x)) x]
      [`(lambda (,x) ,body)
       (closure-fn x body env)]
      [`(zero? ,op)
       (zero? (value-of-fn op env))]
      [`(sub1 ,op)
       (sub1 (value-of-fn op env))]
      [`(* ,op1 ,op2)
       (* (value-of-fn op1 env)
          (value-of-fn op2 env))]
      [`(let ([,var ,exp])
          ,body)
       (value-of-fn body (extend-env 
                          var 
                          (value-of-fn exp env) env))]
      [`(if ,test ,conseq ,alt)
       (if (value-of-fn test env)
           (value-of-fn conseq env)
           (value-of-fn alt env))]
      [`(,rator ,rand)
       (apply-closure-fn
        (value-of-fn rator env)
        (value-of-fn rand env))])))


;;;;;;;;;;;;;;;;;;;;;;;;;     interpreter 2     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define value-of-ds
  (lambda (exp env)
    (pmatch exp
      [`,x (guard (number? x)) x]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`,x (guard (boolean? x)) x]
      [`(lambda (,x) ,body)
       (closure-ds x body env)]
      [`(zero? ,op)
       (zero? (value-of-ds op env))]
      [`(sub1 ,op)
       (sub1 (value-of-ds op env))]
      [`(* ,op1 ,op2)
       (* (value-of-ds op1 env)
          (value-of-ds op2 env))]
      [`(let ([,var ,exp])
          ,body)
       (value-of-ds body (extend-env 
                          var 
                          (value-of-ds exp env) env))]
      [`(if ,test ,conseq ,alt)
       (if (value-of-ds test env)
           (value-of-ds conseq env)
           (value-of-ds alt env))]
      [`(,rator ,rand)
       (apply-closure-ds
        (value-of-ds rator env)
        (value-of-ds rand env))])))


;;;;;;;;;;;;;;;;;;;;;;;;;; interpreter 3  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The interpreters we have been writing so far have been implemented 
;;in such a way that, if there are variables that occur free in a procedure,
;;they take their values from the environment in which the lambda expression 
;;is defined. We accomplish this by creating a closure for each procedure 
;;we see, and we save the environment in the closure. This technique is 
;;called static binding of variables, or static scope.
;;Lexical scope is a kind of static scope.

;;Alternatively, we could implement our interpreters such that 
;;any variables that occur free in the body of a procedure get their values
;;from the environment from which the procedure is called, 
;;rather than from the environment in which the procedure is defined.

(define closure-scopes
  (case-lambda 
    [(x body env)
     `(closure ,x ,body ,env)]
    [(x body)
     `(closure ,x ,body)]))
(define apply-closure-scopes
  (case-lambda 
    [(closure arg newenv)
     (pmatch closure
       [`(closure ,x ,body ,env)
        (value-of-scopes body (extend-env x arg env))]
       [`(closure ,x ,body)
        (value-of-scopes body (extend-env x arg newenv))])]))

(define value-of-scopes
  (lambda (exp env)
    (pmatch exp
      [`,n (guard (number? n)) n]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`(quote ()) '()]
      [`(null? ,ls) 
       (equal? (value-of-scopes ls env) '())]
      [`(cons ,a ,d) 
       (cons (value-of-scopes a env) (value-of-scopes d env))]
      [`(car ,ls) 
       (car (value-of-scopes ls env))]
      [`(cdr ,ls)
       (cdr (value-of-scopes ls env))]
      [`(* ,nexp1 ,nexp2) 
       (* (value-of-scopes nexp1 env) 
          (value-of-scopes nexp2 env))]
      [`(sub1 ,nexp) 
       (sub1 (value-of-scopes nexp env))]
      [`(if ,t ,c ,a) 
       (if (value-of-scopes t env)
           (value-of-scopes c env)
           (value-of-scopes a env))]
      [`(let ((,x ,e)) ,body)
       (let ((a (value-of-scopes e env)))
         (value-of-scopes body (extend-env x a env)))]
      [`(lambda (,x) ,body) 
       (closure-scopes x body env)]
      [`(d-lambda (,x) ,body)
       (closure-scopes x body)]
      [`(,rator ,rand) 
       (apply-closure-scopes
        (value-of-scopes rator env)
        (value-of-scopes rand env)
        env)])))

;;;;;;;;;;;;;;;;;;;;;       interpreter 4     ;;;;;;;;;;;;;;;;;;;;;;;;;;
(define empty-env-fn empty-env)
(define empty-env-ds empty-env)
(define extend-env-fn extend-env)
(define extend-env-ds extend-env)
(define apply-env-fn apply-env)
(define apply-env-ds apply-env)

(define closure-fn-ri
  (lambda (x body env f)   ;; add one more parameter to deal with the body.
    (lambda (arg ext)
      ((f (ext x arg env)) body))))
(define apply-closure-fn-ri
  (lambda (clos arg extend-env) ;; cooperate with closure-fn-ri, add one more parameter.
    (clos arg extend-env)))
(define closure-ds-ri closure-fn-ri)
(define apply-closure-ds-ri apply-closure-fn-ri)

(define value-of-ri
  (lambda (empty-env extend-env apply-env closure apply-closure)
    (letrec ([loop (lambda (env)
                     (lambda (exp)
                       (pmatch exp
                         [`,n (guard (number? n)) n]
                         [`,b (guard (boolean? b)) b]
                         [`,x (guard (symbol? x)) (apply-env env x)]
                         [`(* ,op1 ,op2)
                          (* ((loop env) op1) 
                             ((loop env) op2))]
                         [`(sub1 ,op)
                          ((loop env) op)]
                         [`(zero? ,op)
                          (zero? ((loop env) op))]
                         [`(if ,t ,c ,a)
                          (if ((loop env) t)
                              ((loop env) c)
                              ((loop env) a))]
                         [`(let ([,x ,e])
                             ,body)
                          (let ([val ((loop env) e)])
                            ((loop (extend-env x val)) body))]
                         [`(lambda (,x) ,body)
                          (closure x body env loop)]
                         [`(,rator ,rand)
                          (apply-closure 
                           ((loop env) rator)
                           ((loop env) rand)
                           extend-env)])))])
      (loop (empty-env)))))
;((value-of-ri empty-env-fn extend-env-fn apply-env-fn closure-fn-ri apply-closure-fn-ri) 
; '((lambda (x) x) 5))
;=> 5