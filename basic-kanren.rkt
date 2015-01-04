#lang racket

; Part 1: AND, OR relation using function to represent.

; functions can return more than (or less) one result.
(define fail (lambda (s) '()))         ;; basic construct, like 0 in the natrual nunber.
(define succeed (lambda (s) (list s))) ;; another basic construct.

; relations between two functions, one is disjunction, the other is consjunction
; these are the basic constructs for logic programming.
(define disj
  (lambda (f1 f2)
    (lambda (s)
      (append (f1 s) (f2 s)))))  ; like relation OR

(define conj        ; like relation AND, 
  (lambda (f1 f2)
    (lambda (s)
      (apply append (map f2 (f1 s))))))  ;; only when f1 succeed, then f2 work.
      #;(map f2 (f1 s))  ;; we can't think f2 is just a conj, it could be conj.
; after map, every element in the list is a solution collection! It should be append to
; make up the complete collection.
;;;;;;;;;why need to add (apply append)????
#;((conj (disj succeed succeed) (disj succeed succeed)) 100)
; =>((100 100) (100 100))  but what we need is (100 100 100 100),
; which has fore possible answers.


(define (cout . args)
  (for-each display args))
(define nl #\newline)
#;
(cout "test1" nl 
  ((disj 
     (disj fail succeed) ;; the basic elements can conbine into large complicated system.
     (conj 
       (disj (lambda (x) (succeed (+ x 1)))
	     (lambda (x) (succeed (+ x 10))))
       (disj succeed succeed)))
    100)
  nl)


; Part 2: Logic variable.

(define var (lambda (dumpmy) (vector dumpmy)))
(define var? vector?)

; We use association list of (var . value) as our knowledge about the current world.
; After all, logic programming is about fitting to the world and constrains.

(define empty-subst '())
(define ext-s (lambda (var val s) `((,var . ,val) . ,s)))
(define lookup
  (lambda (var s)
    (cond
      [(not (var? var)) var]
      [(assq var s) => (lambda (p) (lookup (cdr p) s))]
      [else var])))

; return the new substitution, or #f on contradiction.
(define unify
  (lambda (v1 v2 s)
    (let ([v1 (lookup v1 s)]
          [v2 (lookup v2 s)])
      (cond
        [(eq? v1 v2) s]
        [(var? v1)
         (ext-s v1 v2 s)]
        [(var? v2)
         (ext-s v2 v1 s)]
        [(and (pair? v1) (pair? v2))
         (let ([s^ (unify (car v1) (car v2) s)])
           (and s^ (unify (cdr v1) (cdr v2) s^)))]
        [(equal? v1 v2) s]
        [else #f]))))
; defne some global var.
(define vx (var 'x))
(define vy (var 'y))
(define vz (var 'z))
(define vq (var 'q))
(cout "test unify 1:" nl
      (unify 5 5 empty-subst)
      nl)
(cout "test unify 2:" nl
      (unify vx 5 empty-subst)
      nl)
(cout "test unify 3:" nl
      (unify (cons vx vy) (cons 1 vx) empty-subst)
      nl)
(cout "test unify 4:" nl
      (unify (cons vx vy) (cons vy 5) empty-subst)
      nl)

(cout "test unify 5" nl
  (lookup vy (unify vx 1 (unify vx vy empty-subst)))
  nl)


; Part 3: Logic System
; we can combine the non-deterministic function and logic variable to be a Logic system.

; just like monad, we have to make the function as a monad, which accept a substitution,
; and produce some result.
; this is a way to introduce more knowledge into the system, builds up the current 
; substitution.
(define ==
  (lambda (v1 v2)
    (lambda (s)
      (cond
        [(unify v1 v2 s) => succeed]
        [else (fail s)]))))

; and we need a way to run a goal.
; we have to start the run with a sheer inorance.
(define run
  (lambda (g)
    (g empty-subst)))

(run (== 5 5)) ; => (()) means succeed.
(run (== 5 6)) ; => () means fail

(run (disj (== vx 55)
           (== vx 100)))
(run (disj (conj (== vx 55)
                 (== vy (cons vx vy))) ;; HAHA, vy refer to itself, which makes a infinit recursion
           (== vx 100)))           ;; but not until we calculate the value of vy, it's ok.

; using the lambda-abstraction , we can build more complex logic.
; choice: to check if x belongs to ls, if not , fail.
(define choice
  (lambda (x ls)
    (if (null? ls) fail
        (disj
         (== x (car ls))
         (choice x (cdr ls))))))
#;(run (choice vx `(1 ,vy 3 4)))
;=> (((#(x) . 1)) ((#(x) . #(y))) ((#(x) . 3)) ((#(x) . 4)))

; common-el: takes two list, and check if there is a common element.
(define common-el
  (lambda (ls1 ls2)
    (conj
     (choice vx ls1)
     (choice vx ls2))))