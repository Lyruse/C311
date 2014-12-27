; Assignment 2: Free, Bound, and Lexical Address, 
; due Wednesday, September 10th at 11:59pm.

; Author: Lyruse Huang.
; Date: 2014-12-27.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-2



#lang racket
(require C311/pmatch)

;;;;;;;;;;;;;;;;;;Part 1: Natural Recursion Refresher;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 1;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define list-ref:
;        takes a list and a index, then returns the element in the exact
;        place as index.
; !!!!!! Don't need to consider bad data in the definition.
; 
; (listof Any), Number -> Any
(define list-ref
  (lambda (ls n)
    (letrec
        ([nth-cdr
          (lambda (n)
            (cond
              [(zero? n) ls]
              [else (cdr (nth-cdr (- n 1)))]))])
      (car (nth-cdr n)))))
; test:
#;
(list-ref '(a b c) 2) ;=> c
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 2;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define union:
;        takes two lists with no duplicates, and returns a list containing
;        the union of the two input lists.

; (listof Any), (listof Any) -> (listof Any)
(define union
  (lambda (ls1 ls2)
    (cond
      [(null? ls1) ls2]
      [(memv (car ls1) ls2)
       (union (cdr ls1) ls2)]
      [else (cons (car ls1) (union (cdr ls1) ls2))])))
; test:
#;#;
(union '() '())
(union '(x y) '(x z))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 3;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define extend:
;        takes two arguments, say x and pred. 
;        returns another predicate, which satisfied exactly by those things
;        that are eqv? to x or satisfy pred.
;
; Any, Pred -> Pred
(define extend
  (lambda (x pred)
    (lambda (e)
      (or (eqv? e x)
          (pred e)))))
; test:
#;(filter (extend 7 (extend 3 (extend 1 even?))) '(0 1 2 3 4 5))
; =>(0 1 2 3 4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 4;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define walk-symbol:
;        takes a symbol x and an association list s.
;        returns the associated value.
;        if not found the symbol in list, return x.
;
; Symbol, (listof (Symbol . Any)) -> Any
(define walk-symbol
  (lambda (x ls)
    (let ([slot (assv x ls)])
      (cond
        [(not slot) x]
        [(symbol? (cdr slot))
         (walk-symbol (cdr slot) ls)]
        [else (cdr slot)]))))

#;(walk-symbol 'b '((a . 5) (b . ((c . a))) (c . a))) ; =>((c . a))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;           Part 2: Free, bound, lexical address       ;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 5;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define lambda->lumbda:
;        takes a lambda-calculus expression and returns the expression
;        unchanged with the exception that each lambda as a keyword has
;        been replaced with the word lumbda(notice occurrences of lambda 
;        as a variable should be left alone.

; S-exp -> S-exp
(define lambda->lumbda
  (lambda (exp)
    (pmatch exp
      [`,x (guard (not (pair? x))) x]
      [`(lambda (,x) ,body)
       `(lumbda (,x) ,(lambda->lumbda body))]
      [`(,rator ,rand)
       `(,(lambda->lumbda rator)
         ,(lambda->lumbda rand))])))

#; (lambda->lumbda '((lambda (lambda) lambda) (lambda (y) y)))
; => ((lumbda (lambda) lambda) (lumbda (y) y))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;; Assignment 6 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define vars:
;        takes a lambda-calculus expression and returns a list containing
;        all variables that occur in the expression.
;        the order of the vars does not matter.

;     only those used in applications are collected.

; lambda-calculus expressions -> (listof vars)
(define vars
  (lambda (exp)
    (pmatch exp
      [`,x (guard (not (pair? x))) `(,x)]
      [`(lambda (,x) ,body)
       (vars body)]
      [`(,rator ,rand)
       (append (vars rator)
               (vars rand))])))

#; (vars 'x) ;=> (x)
#;  (vars '(lambda (z) ((lambda (y) (a z))
                        (h (lambda (x) (h a))))))
; =>(a z h h a)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;  Assignment 7 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define unique-vars:
;        behaves like vars but only returns a list of var with no duplicates.

; lambda-calculus-exps -> (listof var)
(define unique-vars
  (lambda (exp)
    (pmatch exp
      [`,x (guard (not (pair? x))) `(,x)]
      [`(lambda (,x) ,body)
       (unique-vars body)]
      [`(,rator ,rand)
       (union (unique-vars rator)
              (unique-vars rand))])))

#;(unique-vars '((lambda (a) (a b)) ((lambda (c) (a c)) (b a))))
; => (c b a)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;    Assignment 8     ;;;;;;;;;;;;;;;;;;;;;;;;;
; define var-occurs-free?:
;        takes a symbol and a lambda-calculus expression and returns
;        #t if that variable occurs free in that expression
;        #f otherwise.

; Symbol lambda-calculus-exp -> Boolean

(define var-occurs-free?
  (lambda (v exp)
    (pmatch exp
      [`,x (guard (not (pair? x))) (eq? x v)]
      [`(lambda (,x) ,body)
       (if (eq? x v)
           #f
           (var-occurs-free? v body))]
      [`(,rator ,rand)
       (or (var-occurs-free? v rator)
           (var-occurs-free? v rand))])))

#;(var-occurs-free? 'y '((lambda (y) (x y)) (lambda (x) (x y)))) ;=>#t
#;(var-occurs-free? 'x '(lambda (x) (x y))) ; =>#f
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;   Assignment 9 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define var-occurs-bound?:
;        taks a symbol and a lambda-calculus expression and returns #t
;        if that variable occurs bound in the expression, and #f otherwise

; Symbol, lambda-calculus-exp -> Boolean

(define var-occurs-bound?
  (lambda (v exp)
    (letrec ([f (lambda (flag exp)
                  (pmatch exp
                    [`,x (guard (not (pair? x))) (if flag (eq? x v) #f)]
                    [`(lambda (,x) ,body)
                     (if (eq? x v)
                         (f #t body)
                         (if flag (f #t body)
                             (f #f body)))]
                    [`(,rator ,rand)
                     (or (f flag rator)
                         (f flag rand))]))])
      (f #f exp))))
;; Another version of var-occurs-bound? which uses vars defined previous.
#;
(define var-occurs-bound?
  (lambda (v e)
    (pmatch e
      (`,x (guard (symbol? x)) #f)
      (`(lambda (,x) ,body)
       (cond
         ((memv v (vars body))
          (cond
            ((eq? v x) #t)
            (else (var-occurs-bound? v body))))
         (else #f)))
      (`(,rator ,rand) (or (var-occurs-bound? v rator)
                           (var-occurs-bound? v rand))))))

#;#;#;#;
(var-occurs-bound? 'z '(lambda (y) (lambda (x) (y z))))
#f
(var-occurs-bound? 'z '(lambda (y) (lambda (z) (y z))))
#t
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;             Assignment 10        ;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define unique-free-vars:
;        takes a lambda-calculus-exp and returns a list of all the variables
;        that occur free in that expression.

; lambda-calculus-exp -> (listof var)
(define unique-free-vars
  (lambda (exp)
    (pmatch exp
      [`,x (guard (symbol? x)) `(,x)]
      [`(lambda (,x) ,body)
       (remv x (unique-free-vars body))]
      [`(,rator ,rand)
       (union (unique-free-vars rator)
              (unique-free-vars rand))])))
#;(unique-free-vars '((lambda (x) ((x y) e)) (lambda (c) (x (lambda (x) (x (e c)))))))
; => (y e x)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;        Assignment 11     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define unique-bound-vars:
;        takes a lambda-calculus-exp and returns a list of all the vars that
;        occur bound in the input expression.
;        order doesn't matter, but the list must not contain dup vars.

; lambda-calculus-exp -> (listof var)
(define unique-bound-vars
  (lambda (exp)
    (pmatch exp
      [`,x (guard (symbol? x)) '()]
      [`(lambda (,x) ,body)
       (if (memv x (unique-vars body))
           (cons x (unique-bound-vars body))
           (unique-bound-vars body))]
      [`(,rator ,rand)
       (union (unique-bound-vars rator)
              (unique-bound-vars rand))])))
#;
(unique-bound-vars '((lambda (x) ((x y) e)) (lambda (c) (x (lambda (x) (x (e c)))))))
; =>(x c)
#;
(unique-bound-vars '(lambda (x) y))
; =>()
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;         Assignment 12            ;;;;;;;;;;;;;;;;;;;;;;;;;;
; define lex:
;        takes a lambda-calculus-exp and an accumulator (which starts as the
;        empty list), and returns the same expression with 
;   1) all bound variable references replaced by lists of two elements
;      whose car is the symbol var and whose cadr is the lexical address of
;      the referenced variable
;   2) free variables similarly wrapped within a list whose car is the symbol
;      free-var and whose cadr is the free variable
;   3) the formal parameters of the lambda expressions are dropped.

; lambda-calculus-exp, Accumulator -> lambda-exp
(define lex
  (lambda (exp acc)
    (pmatch exp
      [`,x (guard (symbol? x)) (let ([ret (walk-symbol x acc)])
                                (cond
                                  [(eq? ret x) `(free-var ,x)]
                                  [else `(var ,ret)]))]
      [`(lambda (,x) ,body)
       `(lambda ,(lex body 
                      (cons 
                       (cons x 0)
                       (map
                        (lambda (asso)
                          `(,(car asso) . ,(add1 (cdr asso))))
                        (filter (lambda (asso)
                                 (if (eq? (car asso) x)
                                     #f
                                     #t))
                               acc)))))]
      [`(,rator ,rand)
       `(,(lex rator acc) ,(lex rand acc))])))
#;
(lex '((lambda (x) (x y)) (lambda (c) (lambda (d) (e c)))) '()) 
;=>((lambda ((var 0) (free-var y))) (lambda (lambda ((free-var e) (var 1)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;           Brainteasers !!!! ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define walk*
  (lambda (x s)
    (let ([x (cond [(symbol? x) (walk-symbol x s)]
                   [else x])])
      (cond
        [(pair? x)
         (cons (walk* (car x) s)
               (walk* (cdr x) s))]
        [else x]))))
(define atom? (lambda (x) (and (not (null? x)) (not (pair? x)))))
(define occurs?
  (lambda (a ls)
    (cond
      [(atom? ls) (eq? a ls)]
      [(null? ls) #f]
      [(pair? (car ls))
       (or (occurs? a (car ls))
           (occurs? a (cdr ls)))]
      [else (or (occurs? a (car ls))
                (occurs? a (cdr ls)))])))

; define unify:
;        takes two terms u and v and an association list s.
;        returns #f if u and v are not equivalent
;        otherwise returns s or a extended assoiciation list in which
;        u and v are equivalent.

; Any, Any, (listof (Symbol . Any)) -> #f or (listof (Symbol . Any))
(define unify
  (lambda (u v s)
    (let ([u (walk* u s)]
          [v (walk* v s)])
      (cond
        [(equal? u v) s]
        [(symbol? u)
         (and (not (occurs? u v))
              (cons (cons u v) s))]
        [(symbol? v)
         (and (not (occurs? v u))
              (cons (cons v u) s))]
        [(and (pair? u) (pair? v))
         (let ([s (unify (car u) (car v) s)])
           (and s (unify (cdr u) (cdr v) s)))]
        [else #f]))))
#;
(unify '((x . 5) (y . z)) '((y . 5) (x . 5)) '((z . 5) (x . y))) ;; Another correct answer: ((x . y) (z . 5))
; =>((z . 5) (x . y))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;               Assignment 14                ;;;;;;;;;;;;;;;;;
; define walk-symbol-update:
;        implementing path compression!!!

; Symbol, (listof (Symbol . Box)) -> Any
(define walk-symbol-update
  (lambda (x s)
    (letrec ([f (lambda (x s lis)
                  (let ([slot (assv x s)])
                    (cond
                      [(not slot) x]
                      [(symbol? (unbox (cdr slot)))
                       (f 
                        (unbox (cdr slot)) 
                        s 
                        (cons (cdr slot) lis))]
                      [else (let ([v (unbox (cdr slot))])
                              (map (lambda (e)
                                     (set-box! e v))
                                   lis)
                              v)])))])
      (f x s '()))))
#|
> (define a-list `((c . ,(box 15)) (e . ,(box 'f)) (b . ,(box 'c)) (a . ,(box 'b))))
> a-list
((c . #&15) (e . #&f) (b . #&c) (a . #&b))
> (walk-symbol-update 'a a-list)
15
> a-list
((c . #&15) (e . #&f) (b . #&15) (a . #&15))
> (walk-symbol-update 'a a-list)
15
> a-list
((c . #&15) (e . #&f) (b . #&15) (a . #&15))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;; Assingment 15        Dessert    !!!! ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define var-occurs-both?:
;        returns #t if a var both occur free and occur bound in the lambda-calculus-exp.
;        otherwise #f.

; Symbol, lambda-calculus-exp -> Boolean.
(define var-occurs-both?
  (lambda (x exp)
    (pmatch exp
      [`,x (guard (symbol? x)) #f]
      [`(lambda (,x) ,body)
       ()]
      [`(,rator ,rand)
       ()])))    ;; a little triky, left for tomorow.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;