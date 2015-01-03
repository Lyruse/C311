; Assignment 10: Introduction to Logic Programming

; Author: Lyruse Huang.
; Date: 2015-01-02.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=lp-a2


#lang racket
(require C311/mk)
(require C311/numbers)
(require C311/let-pair)
(require C311/a10-student-tests)
#;(test-file #:file-name "a10.rkt")
(provide (all-defined-out) (all-from-out C311/mk) (all-from-out C311/numbers))

;; Part I Write the answers to the following problems using your
;; knowledge of miniKanren.  For each problem, explain how miniKanren
;; arrived at the answer.  You will be graded on the quality of your
;; explanation; a full explanation will require several sentences.

;; 1 What is the value of 
(run 2 (q)
  (== 5 q)
  (conde
    [(conde [(== 5 q)
	     (== 6 q)])
     (== 5 q)]
    [(== q 5)]))
;;=> (5)
;;after evaluate the goal (== 5 q), q associates to number 5, and evaluate the next
;;goal of conde exptession, which includes two clauses.
;;1) The question of the first clause is another conde expression, which would fail 
;;because of the answer of it associates 6 to q, which conflict with the existed 
;;binding, so the answer of this clause will not be evaluated.
;;2) Then the control comes to second clause which only has question part, it evaluates
;;to be succeed for 5 is the q's associated value.
;;3) Because no other clause can be dived into, So the search ends with q's value of 5.


;; 2 What is the value of
(run 2 (q) 
  (fresh (a b) 
    (== `(,a ,b) q)
    (absento 'tag q)
    (symbolo a)))
; => ((_.0 _.1) (=/= (('tag _.0))) (sym _.0) (absento ('tag _.1)))
;;1) after entering the goals, q is associated with a new variable, then 
;;the first goal ties q to a pair of a b, which are new variables.
;;2) the second goal is constrain that says 'tag can't be anywhere inside q,
;;that means 'tag won't be a part of a or b.
;;3) the last goal says a is bound to be a symbol, which means a can't be 
;;equal to 'tag, so we should add a =/= constrain in the result.

;; 3 What do the following miniKanren constraints mean?
;; a not-pairo ; the thing it applied to must not be a pair.
;; b =/=  ; the two things 
;; c absento
;; d numbero
;; e symbolo

;; Part II goes here.

; utilities
(define conso
  (lambda (a b p)
    (== `(,a . ,b) p)))
(define caro
  (lambda (p a)
    (fresh (d)
           (conso a d p))))
(define cdro
  (lambda (p d)
    (fresh (a)
           (conso a d p))))
(define nullo
  (lambda (ls)
    (== ls '())))
(define assoc
  (lambda (x ls)
    (let-pair ((a . d) ls)
      (let-pair ((aa . da) a)
        (cond
          ((equal? aa x) a)
          ((not (equal? aa x)) (assoc x d)))))))
(define assoco
  (lambda (x ls out)
    (fresh (a d)
           (conso a d ls)
           (fresh (aa ad)
                  (conso aa ad a)
                  (conde
                   [(== aa x)
                    (== out a)]
                   [(assoco x d out)])))))

(define reverse
  (lambda (ls)
    (cond
      ((equal? ls '()) '())
      ((not (equal? ls '()))
       (let-pair ((a . d) ls)
         (let ((res (reverse d)))
           (append res `(,a))))))))
(define reverseo
  (lambda (ls out)
    (conde
     [(nullo ls) (== out '())]
     [(fresh (a d out^)
             (conso a d ls)
             (appendo out^ `(,a) out)
             (reverseo d out^))])))

(define stutter
  (lambda (ls)
    (cond
      ((null? ls) '())
      (else 
        (let-pair ((a . d) ls)
          (let ((res (stutter d)))
            `(,a ,a . ,res)))))))
(define stuttero
  (lambda (ls out)
    (conde
     [(nullo ls) (== out '())]
     [(fresh (a d res)
             (conso a d ls)
             (== out `(,a ,a . ,res))
             (stuttero d res))])))