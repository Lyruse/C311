; Assignment 12: Introduction to Monads

; Author: Lyruse Huang.
; Date: 2015-01-26.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=monads


#lang racket
(require C311/monads)
(require C311/pmatch)
#;(require C311/a12-student-tests)
#;(test-file #:file-name "a12.rkt")
; test result:

;  34 success(es) 0 failure(s) 0 error(s) 34 test(s) run
#;#;#;
(define return-maybe
  (lambda (a) `(Just ,a)))

(define bind-maybe
  (lambda (ma f)
    (cond
      [(eq? (car ma) 'Just) (f (cadr ma))]
      [(eq? (car ma) 'Nothing) '(Nothing)])))

(define fail
  (lambda ()
    '(Nothing)))
;;;;;;;;;;;;;;;;;; 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;
; define assv-maybe:
;   takes an association list and a value to look up.
;   return a value if one is found or '(Nothing) if no match is found in 
;   the list.
#|
> (assv-maybe 'c '((a . 1) (b . 2) (c . 3)))
(Just 3)
> (assv-maybe 'd '((a . 1) (b . 2) (c . 3)))
(Nothing)
|#
(define assv-maybe
  (lambda (v ls)
    (cond
      [(null? ls) (fail)]
      [else 
       (bind-maybe (return-maybe (car ls))
                   (lambda (s)
                     (if (eq? v (car s))
                         (return-maybe (cdr s))
                         (assv-maybe v (cdr ls)))))])))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;#;#;
(define return-writer
  (lambda (a) `(,a . ())))

(define bind-writer
  (lambda (ma f)
    (let ([mb (f (car ma))])
      `(,(car mb) . ,(append (cdr ma) (cdr mb))))))

(define tell-writer
  (lambda (msg)
    `(__ . (,msg))))
;-------------------   Writer Monad ------------------------
;;;;;;;;;;;;;;;;;;;;  2   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define partition-writer:
;  takes a list and a predicate, returning a dotted pair with 
;  the values that do not pass the predicate in the first position
;  and the values that do in the second position.
#|
> (partition-writer even? '(1 2 3 4 5 6 7 8 9 10))
((1 3 5 7 9) . (2 4 6 8 10))
 
> (partition-writer odd? '(1 2 3 4 5 6 7 8 9 10))
((2 4 6 8 10) . (1 3 5 7 9))
|#
(define partition-writer
  (lambda (pred ls)
    (cond
      [(null? ls) (return-writer '())]
      [(pred (car ls))
       (bind-writer (tell-writer (car ls))
                    (lambda (_)   ;; discard the first element in the ma.
                      (partition-writer pred (cdr ls))))]
      [else
       (bind-writer (return-writer (car ls))
                    (lambda (a)   
                      (let ([ret (partition-writer pred (cdr ls))])
                       `(,(cons a (car ret)) . ,(cdr ret)))))])))

(define power
  (lambda (x n)
    (cond
      [(zero? n) 1]
      [(= n 1) x]
      [(odd? n) (* x (power x (sub1 n)))]
      [(even? n) (let ((nhalf (/ n 2)))
                   (let ((y (power x nhalf)))
                     (* y y)))])))
; define powerXpartials:
;  takes a base x and a exponent integer n;
#|
> (powerXpartials 2 6)
(64 . (2 4 8))
 
> (powerXpartials 3 5)
(243 . (3 9 81))
 
> (powerXpartials 5 7)
(78125 . (5 25 125 15625))
|#
(define powerXpartials
  (lambda (x n)
    (cond
      [(zero? n) (return-writer 0)]
      [(= n 1) (return-writer x)]
      [(odd? n) 
       (bind-writer (powerXpartials x (- n 1))
                    (lambda (x^) ; new fix
                      (bind-writer (tell-writer x^)
                                   (lambda (_)
                                     (return-writer (* x x^)))))
                    
                    #;(lambda (a)
                        `(,(* x a) . (,(* x a)))))]
      [(even? n)
       (bind-writer (powerXpartials x (/ n 2))
                    (lambda (x^)  ; new fix
                      (bind-writer (tell-writer x^)
                                   (lambda (_)
                                     (return-writer (* x^ x^)))))
                    
                    #;(lambda (a)
                        `(,(* a a) . (,(* a a)))))])))
;> (powerXpartials 5 7) ; before fix
;(78125 25 125 15625 78125) ; has an addition last value.
#;
(define powerXpartials ; use do notation.
  (lambda (x n)
    (cond
      [(zero? n) (return-writer 0)]
      [(= n 1) (return-writer x)]
      [(odd? n) 
       (do bind-writer
         (x^ <- (powerXpartials x (sub1 n)))
         (tell-writer x^)
         (return-writer (* x x^)))]
      [(even? n)
       (do bind-writer
         (x^ <- (powerXpartials x (/ n 2)))
         (tell-writer x^)
         (return-writer (* x^ x^)))])))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;------------------- State Monad ----------------------------
#;#;#;#;
(define return-state
  (lambda (a)
    (lambda (s)
      `(,a . ,s))))

(define bind-state
  (lambda (ma f)
    (lambda (s)
      (let ([vs^ (ma s)])
        (let ([v (car vs^)]
              [s^ (cdr vs^)])
          ((f v) s^))))))

(define get-state
  (lambda (s) `(,s . ,s)))

(define put-state
  (lambda (new-s)
    (lambda (s)
      `(__ . ,new-s))))
;;;;;;;;;;;;;;;;;;;;;;;;;  abc-game ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
> ((abc-game '(a b c c b a)) 0) ; seen a +1 , seen b -1, seen c unchange.
(__ . 0)
 
> ((abc-game '(a b c c b a a)) 0)
(__ . 1)
 
> ((abc-game '(a a a)) 0)
(__ . 3)
|#
(define abc-game
  (lambda (ls)
    (cond
      [(null? ls) (return-state '__)]
      [(eq? 'a (car ls))
       #;
       (bind-state (lambda (s) `(__ . ,(+ s 1)))
                   (lambda (_)
                     (abc-game (cdr ls))))
       (do bind-state
         (n <- (abc-game (cdr ls)))
         (s <- get-state)
         (put-state (add1 s))
         (return-state n))]
      [(eq? 'b (car ls))
       (bind-state (lambda (s) `(__ . ,(- s 1)))
                   (lambda (_)
                     (abc-game (cdr ls))))]
      [(eq? 'c (car ls))
       #;(bind-state (lambda (s) `(__ . ,s))
                     (lambda (_)
                       (abc-game (cdr ls))))
       (abc-game (cdr ls))])))
;-------------------------------------------------------------------


;----------------------     Mixed Monads Problems      ----------------------
(define traverse
  (lambda (return bind f)
    (letrec
        ((trav
          (lambda (tree)
            (cond
              [(pair? tree)
               (do bind
                 (a <- (trav (car tree)))
                 (d <- (trav (cdr tree)))
                 (return (cons a d)))]
              [else (f tree)]))))
      trav)))

;;;;;;;;;;;;;;;;;;;;;;  reciprocal  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define reciprocal:
;  takes a number n, return (/ 1 n). if it encounters 0, then return (Nothing).
(define reciprocal
  (lambda (n)
    (cond
      [(zero? n) (fail)]
      [else (return-maybe (/ 1 n))])))
(define traverse-reciprocal
  (traverse return-maybe bind-maybe reciprocal))

;;;;;;;;;;;;;;;;;;;;;;;;;;    Halve    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define halve:
;  takes a number, either will return in the monad half the number, or; 
;  if the number is not divisible by two, will instead leave the original
;  number in place and also log that number(using writer monad).
; (halve 5) => (5 . (5))
(define halve
  (lambda (n)
    (cond
      [(even? n) (return-writer (/ n 2))]
      [else (bind-writer (tell-writer n)
                         (lambda (_)
                           (return-writer n)))])))
(define traverse-halve
  (traverse return-writer bind-writer halve))
;> (traverse-halve '((1 . 2) . (3 . (4 . 5))))
;(((1 . 1) . (3 . (2 . 5))) . (1 3 5))


;;;;;;;;;;;;;;;;;;;;;;;;;  state/sum   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;define state/sum:
;  takes a number, return the current state as the value,
;  and add that number to the current state.
#|
> ((state/sum 2) 0)
(0 . 2)
 
> ((state/sum 2) 3)
(3 . 5)
|#

(define state/sum
  (lambda (n)
    (lambda (s)
      ((return-state s) (+ n s)))))
(define traverse-state/sum
  (traverse return-state bind-state state/sum))
; ((traverse-state/sum '((1 . 2) . (3 . (4 . 5)))) 0)
;=>(((0 . 1) 3 6 . 10) . 15)
;----------------------------------------------------------------------------








;----------------------------- CPS Monad Interpreter -----------------------------
(define empty-env (lambda () '()))
(define extend-env (lambda (x v env) `((,x . ,v) . ,env)))
(define apply-env (lambda (env x) (pmatch env
                                    [`((,x^ . ,v) . ,env)
                                     (if (eq? x x^)
                                         v
                                         (apply-env env x))])))
(define closure (lambda (arg body env)
                  `(,arg ,body ,env)))
(define apply-proc (lambda (clo val)
                     (pmatch clo
                       [`(,arg ,body ,env)
                        (value-of body (extend-env arg val env))])))
(define value-of
  (lambda (expr env)
    (pmatch expr
      [`,n (guard (or (number? n) (boolean? n))) n]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`(* ,x1 ,x2) (* (value-of x1 env) (value-of x2 env))]
      [`(sub1 ,x) (sub1 (value-of x env))]
      [`(zero? ,x) (zero? (value-of x env))]
      [`(if ,test ,conseq ,alt) (if (value-of test env)
                                    (value-of conseq env)
                                    (value-of alt env))]
      [`(capture ,k-id ,body) (call/cc (lambda (k)
                                         (value-of body (extend-env k-id k env))))]
      [`(return ,v-exp ,k-exp) ((value-of k-exp env) (value-of v-exp env))]
      [`(lambda (,id) ,body) (closure id body env)]
      [`(,rator ,rand) (apply-proc (value-of rator env) (value-of rand env))])))






(define apply-proc-cps (lambda (clo val)
                     (pmatch clo
                       [`(,arg ,body ,env)
                        (value-of-cps body (extend-env arg val env))])))
(define value-of-cps
  (lambda (expr env)
    (pmatch expr
      [`,n (guard (or (number? n) (boolean? n))) (return-cont n)]
      [`,x (guard (symbol? x)) (return-cont (apply-env env x))]
      [`(* ,x1 ,x2) (bind-cont (value-of-cps x1 env)
                               (lambda (x1)
                                 (bind-cont (value-of-cps x2 env)
                                            (lambda (x2)
                                              (return-cont (* x1 x2))))))]
      [`(sub1 ,x) (do bind-cont 
                    (x <- (value-of-cps x env))
                    (return-cont (sub1 x)))]
      [`(zero? ,x) (do bind-cont 
                    (x <- (value-of-cps x env))
                    (return-cont (zero? x)))]
      [`(if ,test ,conseq ,alt) (do bind-cont 
                                  (res <- (value-of-cps test env))
                                  (if res
                                      (value-of-cps conseq env)
                                      (value-of-cps alt env)))]
      [`(capture ,k-id ,body) (callcc (lambda (out)
                                        (value-of-cps body (extend-env k-id out env))))]
      [`(return ,v-exp ,k-exp) (do bind-cont
                                 (k <- (value-of-cps k-exp env))
                                 (a <- (value-of-cps v-exp env))
                                 (k a))]
      [`(lambda (,id) ,body) (return-cont (closure id body env))]
      [`(,rator ,rand) (do bind-cont
                         (r <- (value-of-cps rator env))
                         (d <- (value-of-cps rand env))
                         (apply-proc-cps r d))])))

(define fact-5   ;; for test
  '((lambda (f)
      ((f f) 5))
    (lambda (f)
      (lambda (n)
        (if (zero? n)
            1
            (* n ((f f) (sub1 n))))))))
;> ((value-of-cps fact-5 (empty-env)) (lambda (v) v))
;120
(define capture-fun  ;; for test
  '(* 3 (capture q (* 2 (return 4 q)))))
;> ((value-of-cps capture-fun (empty-env)) (lambda (v) v))
;12



#|
Just Dessert: The Fringe
Like baking soda, the traverse function above has many applications. Here's one more.
 We're going to use the Cont monad to achieve a kind of trampolining or multitasking.

The fringe of a tree is the list of its leaves in left-to-right order. For example, 
the fringe of

(("Time" . "flies") . ("like" . ("an" . "arrow")))
is the list of strings

("Time" "flies" "like" "an" "arrow")
Given two trees, the driver function compares their fringes 
while ignoring any differences in capitalization. If the two fringes are the same, 
then driver returns the two trees (in a list) with their leaves swapped.
 If the two fringes have bigger differences than mere capitalization, 
then driver returns #f.

For example, here are two tests:

 
> (driver '(("Time" . "flies") . ("like" . ("an" . "arrow")))
	  '("time" . ("FLIES" . (("like" . "an") . "aRrOw"))))
((("time" . "FLIES") . ("like" . ("an" . "aRrOw")))
 ("Time" . ("flies" . (("like" . "an") . "arrow"))))
 
> (driver '(("Time" . "flies") . ("like" . ("arrow" . "an")))
          '("time" . ("FLIES" . (("like" . "an") . "aRrOw"))))
#f
Below is most of the definition of driver. Your mission is
 to complete the definition by defining yield-cont.
|#

(define exchange
  (lambda ($1 $2)
    (pmatch `(,$1 ,$2)
      [`((stopped ,tree1) (stopped ,tree2))
       `(,tree1 ,tree2)]
      [`((yielding ,x1 ,k1) (yielding ,x2 ,k2))
       (guard (string-ci=? x1 x2))
       (exchange (k1 x2) (k2 x1))]
      [else #f])))
#;
(define traverse
  (lambda (return bind f)
    (letrec
        ((trav
          (lambda (tree)
            (cond
              [(pair? tree)
               (do bind
                 (a <- (trav (car tree)))
                 (d <- (trav (cdr tree)))
                 (return (cons a d)))]
              [else (f tree)]))))
      trav)))
(define tree->stream
  (lambda (tree)
    (((traverse return-cont bind-cont yield-cont)
      tree)
     (lambda (tree) `(stopped ,tree)))))
(define driver
  (lambda (tree1 tree2)
    (exchange (tree->stream tree1) (tree->stream tree2))))

(define yield-cont      ;; it seems a bit too easy.
  (lambda (leave)
    (lambda (k)
      `(yielding ,leave ,k))))