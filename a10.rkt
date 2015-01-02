; Assignment 10: Introduction to Logic Programming

; Author: Lyruse Huang.
; Date: 2015-01-02.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=lp-a2


#lang racket
(require C311/mk)
(require C311/numbers)
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
;;=> 
;;
;;
;;
;;

;; 3 What do the following miniKanren constraints mean?
;; a not-pairo
;; b =/=
;; c absento
;; d numbero
;; e symbolo

;; Part II goes here.

