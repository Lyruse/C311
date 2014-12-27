; Author: Lyruse Huang.
; Date: 2014-12-27.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-1



#lang racket

; Assignment 1
; define countdown: takes a natural number and returns a list of 
; natural numbers less than or equal to that number, in descending order.
; 
; Number -> (listof Number)
;
; (countdown 5) => (5 4 3 2 1 0)
(define countdown
  (lambda (n)
    (cond
      [(= n 0) '(0)]
      [else (cons n (countdown (- n 1)))])))


; Assignment 2
; define insertR:
;        takes two symbols and a list and returns a new list with second
;        symbol inserted after each occurence of the first symbol.
;
; Symbol, Symbol, (listof Symbol) -> (listof Symbol)
;
; (insertR 'key 'new '(key 2)) => '(key new 2)
; First Edition, improve it with internal function.
#;
(define insertR
  (lambda (key new ls)
    (cond
      [(null? ls) '()]
      [(eq? key (car ls))
       (cons key (cons new (insertR key new (cdr ls))))]
      [else (cons (car ls) (insertR key new (cdr ls)))])))
(define insertR
  (lambda (key new ls)
    (letrec ([f (lambda (ls)
                  (cond
                    [(null? ls) '()]
                    [(eq? key (car ls))
                     (cons key (cons new (f (cdr ls))))]
                    [else (cons (car ls) (f (cdr ls)))]))])
      (f ls))))

(define insertR-fr
  (lambda (key new ls)
    (foldr (lambda (e pre) 
             (cond
               [(eq? key e) (cons key (cons new pre))]
               [else (cons e pre)]))
           '()
           ls)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Assignment 3
; define remv-1st:
;        takes a symbol and a list and returns a new list with the first
;        occurence of the symbol removed.
;
; Symbol, (listof Symbol) -> (listof Symbol)
;
; (remv-1st 'hello '(world is saying hello hello)) => '(world is saying hello)
(define remv-1st
  (lambda (a ls)
    (cond
      [(null? ls) '()]
      [(eq? a (car ls))
       (cdr ls)]
      [else (cons (car ls) (remv-1st a (cdr ls)))])))


; Assignment 4
; define occurs-?s:
;        takes a list and returns the number of times the symbol? occurs
;        in the list.
; (listof Any) -> Number
(define occurs-?s
  (lambda (ls)
    (cond
      [(null? ls) 0]
      [(eq? '? (car ls))
       (+ 1 (occurs-?s (cdr ls)))]
      [else (occurs-?s (cdr ls))])))
; test:
#;(occurs-?s '(? y z ? ?)) ; => 3
(define occurs-?s-fr
  (lambda (ls)
    (foldr (lambda (e n)
             (cond
               [(eq? '? e) (+ 1 n)]
               [else n]))
           0
           ls)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 5;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define filter:
;        takes a predicate and a list and returns a new list containing the 
;        elements that satisfy the predicate.
;        A predicate is a procedure that takes a single argument and return
;        either #t or #f.
;
; Procedure, (listof Any) -> (listof Any)
(define filter
  (lambda (f ls)
    (cond
      [(null? ls) '()]
      [(f (car ls))
       (cons (car ls) (filter f (cdr ls)))]
      [else (filter f (cdr ls))])))
; test:
#;(filter even? '(1 2 3 4 5 6)) ;=> (2 4 6)
(define filter-fr
  (lambda (f ls)
    (foldr (lambda (e pre)
             (cond
               [(f e)
                (cons e pre)]
               [else pre]))
           '()
           ls)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 6;;;;;;;;;;;;;;;;;;;;;;;;;
; define zip:
;        takes two lists of equal length and forms a new list,
;        each element of which ia s pair formed by combining the 
;        corresponding elements of the two input lists.
;
; (listof Any), (listof Any) -> (listof '(Any Any))
(define zip
  (lambda (l1 l2)
    (cond
      [(null? l1) '()]
      [else (cons (cons (car l1) (car l2))
                  (zip (cdr l1) (cdr l2)))])))
;test:
#;(zip '(1 2 3) '(a b c)) ; => ((1 . a) (2 . b) (3 . c)
(define zip-fr
  (lambda (ls1 ls2)
    (foldr (lambda (e1 e2 pre)
             (cons (cons e1 e2) pre))
           '()
           ls1 ls2)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 7;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define map:
;        takes a procedure p of one argument and a list and returns a new
;        list containing the results of applying p to the elements of ls.
;
; Procedure, (listof Any) -> (listof Any)
(define map
  (lambda (f ls)
    (cond
      [(null? ls) '()]
      [else (cons (f (car ls))
                  (map f (cdr ls)))])))
; test:
#;(map add1 '(1 2 3 4)) ; => (2 3 4 5)
(define map-fr
  (lambda (f ls)
    (foldr (lambda (e pre)
             (cons (f e) pre))
           '()
           ls)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 8;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define append:
;        takes two lists, ls1 and ls2, and append ls1 to ls2.

; (listof Any), (listof Any) -> (listof Any)
(define append
  (lambda (ls1 ls2)
    (cond
      [(null? ls1) ls2]
      [else (cons (car ls1)
                  (append (cdr ls1) ls2))])))
;test:
#;
(append '(a b c) '(1 2 3)) ; => (a b c 1 2 3)
(define append-fr
  (lambda (ls1 ls2)
    (foldr (lambda (e pre)
             (cons e pre))
           ls2
           ls1)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 9;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define reverse:
;        takes a list and returns the reverse of that list.
;
; (listof Any) -> (listof Any)
(define reverse
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [else (append (reverse (cdr ls)) `(,(car ls)))])))
; test:
#;
(reverse '(a 3 x)) ; => (x 3 a)
(define reverse-fr
  (lambda (ls)
    (foldr (lambda (e pre)
             (append pre `(,e)))
           '()
           ls)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 10;;;;;;;;;;;;;;;;;;;;;;;;;;
; define fact:
;        takes a natural number and computes the factorial of that number.
;
; Number -> Number
(define fact
  (lambda (n)
    (cond
      [(= 1 n) 1]
      [else (* n (fact (- n 1)))])))
; test:
#;
(fact 5) ; => 120
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assigment 11;;;;;;;;;;;;;;;;;;;;;;;;;
; define member-?*:
;        taks a list and returns #t if the list contains the symbol ?,
;        #f otherwise.
; (listof Any) -> Boolean
(define member-?*
  (lambda (ls)
    (cond
      [(null? ls) #f]
      [(pair? (car ls))
       (or (member-?* (car ls))
           (member-?* (cdr ls)))]
      [(eq? '? (car ls))
       #t]
      [else (member-?* (cdr ls))])))
; test:
#;
(member-?* '((a ((?)) ((c) b c)))) ; => #t
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 12;;;;;;;;;;;;;;;;;;;;;;;
; define fib:
;        takes a natural number n as input and computes the nth number,
;        starting from zero, in the Fibonacci sequence (0, 1, 1, 2, 3,...)
; Number -> Number
(define fib
  (lambda (n)
    (cond
      [(< n 2) n]
      [else (+ (fib (- n 1))
               (fib (- n 2)))])))
; test:
#;
(fib 7) ; => 13
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assigment 13;;;;;;;;;;;;;;;;;;;;;;;;
; rewrite ((w x) y (z)) to dotted expression.
#; 
(equal? '((w x) y (z)) '((w . (x . ())) . (y . ((z . ()) . ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 14;;;;;;;;;;;;;;;;;;;;;;;;
; define binary->natural:
;        takes a flat list of 0s and 1s representing an unsigned binary
;        number in reverse bit order and returns that number.
;
; (listof Bit) -> Number
(define binary->natural
  (lambda (ls)
    (cond
      [(null? ls) 0]
      [else                ; the input must be either 0 or 1;
       (+ (car ls) (* 2 (binary->natural (cdr ls))))])))
; test:
#;
(binary->natural '(1 1 1 1 1 1 1 1 1 1 1 1 1))

(define binary->natural-fr
  (lambda (ls)
    (cdr
     (foldr (lambda (e pre)
              `(,(* 2 (car pre)) . ,(+ (* e (* 2 (car pre))) (cdr pre))))
            '(1/2 . 0)
            (reverse ls)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 15;;;;;;;;;;;;;;;;;;;;;;
; define minus:
;        using natual recursion to define subtraction.
;        input and returns are all nonnegative.

; Number, Number -> Number
(define minus
  (lambda (l r)
    (cond
      [(= 0 r) l]
      [else (+ -1 (minus l (- r 1)))])))
; test:
#;
(minus 100 50) ; => 50
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 16;;;;;;;;;;;;;;;;;;;;;;;;;
; define div:
;        using natural recursion to define division.
;        need only work when the second number evenly divides the first
;        division by zero is of course bad data.
;
; Number, Number -> Number
(define div
  (lambda (l r)
    (cond
      [(= 0 l) 0]
      [else (+ 1 (div (- l r) r))])))
; test:
#;
(div 36 6)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 18;;;;;;;;;;;;;;;;;;;;;;
;define fact-acc:
;       takes a number and return the factorial result of it
;       but use tail recursive.
; Number -> Number

(define fact-acc
  (lambda (n acc)
    (cond
      [(zero? n) acc]
      [else (fact-acc (- n 1) (* n acc))])))
;test:
#;
(fact-acc 5 1) ; => 120
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 19;;;;;;;;;;;;;;;;;;;;;;;;
; define power:
;        takes a base b and a power n, compute the power of base b.
;
; Number, Number -> Number
(define power
  (lambda (x n)
    (cond
      [(zero? n) 1]
      [(odd? n)
       (* x (power x (- n 1)))]
      [else (let ([s (power x (/ n 2))])
              (* s s))])))
;test:
#;
(power 2 10) ;=> 1024
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 20;;;;;;;;;;;;;;;;;;;;;;;;;;;
; define natural->binary:
;        takes a number and returns a flat list of 0s and 1s representing
;        that unsigned binary number in reverse bit order.
;
; Number -> (listof Bit)
(define natural->binary
  (lambda (n)
    (cond
      [(zero? n) '()]
      [(odd? n) (cons 1 (natural->binary (quotient n 2)))]
      [else (cons 0 (natural->binary (quotient n 2)))])))
; test:
#;
(natural->binary 21) ;=> '(1 0 1 0 1)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 21;;;;;;;;;;;;;;;;;;;;;;;;
(define base
  (lambda (x)
    (error 'error "Invalid value ~s~n" x)))
 
(define odd-case
  (lambda (recur)
    (lambda (x)
      (cond 
        ((odd? x) (collatz (add1 (* x 3)))) 
        (else (recur x))))))
 
(define even-case
  (lambda (recur)
    (lambda (x)
      (cond 
        ((even? x) (collatz (/ x 2))) 
        (else (recur x))))))
 
(define one-case
 (lambda (recur)
   (lambda (x)
     (cond
       ((zero? (sub1 x)) 1)
       (else (recur x))))))
(define collatz
  (lambda (n)
    ((one-case (even-case (odd-case base))) n)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;Just Dessert;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define quine ((lambda (x) (list x (list 'quote x)))
               '(lambda (x) (list x (list 'quote x)))))




#;#;
(define myfoldr
  (lambda (f firt ls)
    (cond
      [(null? ls) firt]
      [else (f (car ls) (myfoldr f firt (cdr ls)))])))
(define myfoldl
  (lambda (f firt ls)
    (cond
      [(null? ls) firt]
      [else (myfoldl f (f (car ls) firt) (cdr ls))])))
#;(require "a1-student-tests.rkt")
#;(test-file #:file-name "a1.rkt")
