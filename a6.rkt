; Assignment 6: Continuation-Passing Style

; Author: Lyruse Huang.
; Date: 2014-12-30.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-6

#lang racket
(require C311/pmatch)
#;(require C311/a6-student-tests)
#;(test-file)
;; test result: 
;; 7 success(es) 0 failure(s) 0 error(s) 7 test(s) run. Perfect.
;; All program are real Continuation passing style.

; since I have learned a lot from Yinwang's cpser, which enables me to write a cpser
; myself, so this Assignment seems meaningless to me, but I will still quickly walk this
; Assignment through, to enhance my understanding about continuation passing style.
; As I read the Chapter 5 of SICP, I found it cps is really like making a register 
; machine myself, I have to maintain the stack structure as cps.

(define empty-k
  (lambda ()
    (let ([once-only #f])
      (lambda (v)
        (if once-only
            (error 'empty-k "You can only invoke the emtpy continuation once.")
            (begin (set! once-only #t) v))))))


;; ======================== A 1 ============================
; define last-non-zero:
;   takes a list of numbers and returns the last cdr whose car is 0.

; (listof Number) -> (listof Number)
(define last-non-zero
  (lambda (ls)
    (call/cc (lambda (k)
               (letrec ([f (lambda (ls)  ; it seems a little too tedious.
                             (cond       ; too many k around.
                               [(null? ls) '()]
                               [(zero? (car ls)) (k (f (cdr ls)))]
                               [else (cons (car ls) (f (cdr ls)))]))])
                 (f ls))))))
#;  (last-non-zero '(1 0 2 3 0 4 5))
; => (4 5)

(define last-non-zero2
  (lambda (ls)
    (call/cc (lambda (return)
               (letrec ([f (lambda (ls k)
                             (cond
                               [(null? ls) (k '())]
                               [(zero? (car ls)) (f (cdr ls) return)]
                               [else (f (cdr ls) 
                                        (lambda (r)
                                          (k (cons (car ls) r))))]))])
                 (f ls return))))))

; ========================== A 2 =================================
(define mult/cc
  (lambda (ls)
    (call/cc
     (lambda (return)
       (letrec ([f (lambda (ls)
                     (cond
                       [(null? ls) 1]
                       [(zero? (car ls)) (return 0)]
                       [else (* (car ls) (f (cdr ls)))]))])
         (f ls))))))


; =========================== Part 2 ==============================


;============================== A 3 ===============================
(define times
  (lambda (ls)
    (cond
      [(null? ls) 1]
      [(zero? (car ls)) 0]
      [else (* (car ls) (times (cdr ls)))])))
(define times-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k 1)]
      [(zero? (car ls)) 0]
      [else (times-cps (cdr ls) (lambda (r)
                                  (k (* (car ls) r))))])))
;============================== A 4 ==============================
; I just did the requirement in the A 3 .

;===============================A 5 ==============================
(define plus
  (lambda (m)
    (lambda (n)
      (+ m n))))
(define plus-cps
  (lambda (m k)
    (k (lambda (n k)
         (k (+ m n))))))
#;((plus-cps 10 (empty-k)) 5 (empty-k)) ; => 15

; ===========================  A  6 =================================
(define count-syms*
  (lambda (ls)
    (cond
      [(null? ls) 0]
      [(pair? (car ls)) (+ (count-syms* (car ls))
                           (count-syms* (cdr ls)))]
      [(symbol? (car ls)) (add1 (count-syms* (cdr ls)))]
      [else (count-syms* (cdr ls))])))

(define count-syms*-cps
  (lambda (ls k)
    (cond
      [(null? ls) (k 0)]
      [(pair? (car ls))
       (count-syms*-cps (car ls)
                    (lambda (a)
                      (count-syms*-cps (cdr ls)
                                   (lambda (d)
                                     (k (+ a d))))))]
      [(symbol? (car ls)) (count-syms*-cps (cdr ls)
                                       (lambda (d)
                                         (k (add1 d))))]
      [else (count-syms*-cps (cdr ls)
                         (lambda (d)
                           (k d)))])))

; ===============================  A 7 =================================
(define cons-cell-count
  (lambda (ls)
    (cond
      [(pair? ls) 
       (add1 (+ (cons-cell-count (car ls)) (cons-cell-count (cdr ls))))]
      [else 0])))

(define cons-cell-count-cps
  (lambda (ls k)
    (cond
      [(pair? ls)
       (cons-cell-count-cps (car ls)
                            (lambda (a)
                              (cons-cell-count-cps (cdr ls)
                                                   (lambda (d)
                                                     (k (add1 (+ a d)))))))]
      [else (k 0)])))

;the cons-cell-count-cps didn't make the cond expression cps, which the interpreter
;builds up the continuation for us.

; ============================= A 8 ======================================
(define walk
  (lambda (v ls)
    (cond
      [(symbol? v)
       (let ([p (assq v ls)]) ; if not exist , return #f
         (cond
           [p (walk (cdr p) ls)]
           [else v]))]
      [else v])))

(define walk-cps
  (lambda (v ls k)
    (cond
      [(symbol? v)
       (let ([p (assq v ls)])
         (cond
           [p (walk-cps (cdr p) ls k)]
           [else (k v)]))]
      [else (k v)])))

;;========================== A 9 ===========================================
(define ack
  (lambda (m n)
    (cond
      [(zero? m) (add1 n)]
      [(zero? n) (ack (sub1 m) 1)]
      [else (ack (sub1 m)
                 (ack m (sub1 n)))])))

(define ack-cps
  (lambda (m n k)
    (cond
      [(zero? m) (k (add1 n))]
      [(zero? n) (ack-cps (sub1 m) 1 k)]
      [else (ack-cps m (sub1 n) (lambda (n)
                              (ack-cps (sub1 m) n k)))])))

;;=========================A 10=================================================
(define fib
  (lambda (n)
    ((lambda (fib)
       (fib fib n))
     (lambda (fib n)
       (cond
         [(zero? n) 0]
         [(= 1 n) 1]
         [else (+ (fib fib (sub1 n)) (fib fib (sub1 (sub1 n))))])))))
(define fib-cps
  (lambda (n k)
    ((lambda (fib k)
       (fib fib n k))
     (lambda (fib n k)
       (cond
         [(zero? n) (k 0)]
         [(= 1 n) (k 1)]
         [else (fib fib (sub1 n) (lambda (a)
                                   (fib fib (sub1 (sub1 n))
                                        (lambda (d)
                                          (k (+ a d))))))]))
     k)))

;============================= A 11 ==============================================
(define unfold
  (lambda (p f g seed)
    ((lambda (h)
       ((h h) seed '()))
     (lambda (h)
       (lambda (seed ans)
         (if (p seed)
             ans
             ((h h) (g seed) (cons (f seed) ans))))))))
(define null?-cps
  (lambda (ls k)
    (k (null? ls))))
(define car-cps
  (lambda (pr k)
    (k (car pr))))
(define cdr-cps
  (lambda (pr k)
    (k (cdr pr))))
(define unfold-cps   ;; I'am so impressed, I did write it with a clear principle.
  (lambda (p f g seed return)
    ((lambda (h k)
       (h h (lambda (rator)
              (rator seed '() k))))
     (lambda (h k)
       (k (lambda (seed ans k1)
            (p seed (lambda (t)
                      (if t
                          (k1 ans)
                          (h h (lambda (rator)
                                 (g seed (lambda (rest)
                                           (f seed (lambda (e)
                                                     (rator rest (cons e ans) k1)))))))))))))
     return)))
#; (unfold-cps null?-cps car-cps cdr-cps '(a b c d e) (empty-k))
; =>(e d c b a)

; ============================== A 12 ===========================================
(define empty-s
  (lambda ()
    '()))
(define extend-s
  (lambda (x v s)
    `((,x . ,v) . ,s)))
(define unify
  (lambda (v w s)
    (let ([v (walk v s)]
          [w (walk w s)])
      (cond
        [(eqv? v w) s]
        [(symbol? v) (extend-s v w s)]
        [(symbol? w) (extend-s w v s)]
        [(and (pair? v) (pair? w))
         (let ([s^ (unify (car v) (car w) s)])
           (and s^ (unify (cdr v) (cdr w) s^)))]
        [(equal? v w) s]
        [else #f]))))
#;(unify '(x y z) '(5 x y) (empty-s))
; =>((z . 5) (y . 5) (x . 5))
(define unify-cps
  (lambda (v w s k)
    (walk-cps v s 
              (lambda (v)
                (walk-cps w s
                          (lambda (w)
                            (cond           ;; this should be transformed to if exps.
                              [(eqv? v w) (k s)]
                              [(symbol? v) (k (extend-s v w s))]
                              [(symbol? w) (k (extend-s w v s))]
                              [(and (pair? v) (pair? w))
                               (unify-cps (car v) (car w) s
                                      (lambda (s^)
                                        (if s^
                                            (unify-cps (cdr v) (cdr w) s^ 
                                                       (lambda (s^^) ;eta reduction.
                                                         (k s^^)))
                                            #f)))]
                              [(equal? v w) (k s)]
                              [else (k #f)])))))))
#;(unify-cps '(x y z) '(5 x y) (empty-s) (empty-k))
; =>((z . 5) (y . 5) (x . 5))

;========================== A 13 =====================================
(define M
  (lambda (f)
    (lambda (ls)
      (cond
        [(null? ls) '()]
        [else (cons (f (car ls)) ((M f) (cdr ls)))]))))

(define M-cps
  (lambda (f k)
    (k (lambda (ls k)
         (cond
           [(null? ls) (k '())]
           [else (f (car ls)
                    (lambda (a)
                      (M-cps f (lambda (loop)
                                 (loop (cdr ls)
                                       (lambda (d)
                                         (k (cons a d))))))))])))))
#;((M-cps car-cps (empty-k)) '((1 2) (3 4) (5 6)) (empty-k))
; => (1 3 5)

; ======================== A 14 ============================================
(define use-of-M
  ((M (lambda (n) (add1 n))) '(1 2 3 4 5)))
(define use-of-M-cps
  ((M-cps car-cps (empty-k)) '((1 2) (3 4) (5 6) (7 8)) (empty-k)))

; ======================== A 15 ============================================
(define strange
  (lambda (x)
    ((lambda (g) (lambda (x) (g g)))
     (lambda (g) (lambda (x) (g g))))))
(define strange-cps
  (lambda (x k)
    ((lambda (g k) (k (lambda (x k) (g g k))))
     (lambda (g k) (k (lambda (x k) (g g k))))
     k)))
; ========================= A 16 =========================================
(define use-of-strange
  (let ([strange^ (((strange 5) 6) 7)])
    (((strange^ 8) 9) 10)))
(define use-of-strange-cps
  ((strange-cps 100 (empty-k)) 100 (empty-k)))

;================================ A 17 ==================================
(define why
  (lambda (f)
    ((lambda (g)
       (f (lambda (x) ((g g) x))))
     (lambda (g)
       (f (lambda (x) ((g g) x)))))))
(define why-cps
  (lambda (f k)
    ((lambda (g k)
       (f (lambda (x k) (g g (lambda (hehe) (hehe x k))))
          k))
     (lambda (g k)
       (f (lambda (x k) (g g (lambda (hehe) (hehe x k))))
          k))
     k)))
(define almost-length
  (lambda (f)
    (lambda (ls)
      (if (null? ls)
          0
          (add1 (f (cdr ls)))))))
(define almost-length-cps
  (lambda (f k)
    (k (lambda (ls k)
         (if (null? ls)
             (k 0) ; miss the k, fuck it!
             (f (cdr ls)
                (lambda (x)
                  (k (add1 x)))))))))
#;((why almost-length) '(a b c d e f))
; =>6
#;
(why-cps almost-length-cps (lambda (f) ;; not work yet, don't know why, 'll figure it out.
                               (f '(1 2 3) (empty-k))))
; ==> 3
; ========================= A 18 ===============================
; so easy.
(define why-cps-cps
  (lambda (f k0 k1)
    ((lambda (g k0 k1)
       (f (lambda (x k kk) (g g (lambda (hehe kkk) (hehe x k kkk)) kk))
          k0 k1))
     (lambda (g k0 k1)
       (f (lambda (x k kk) (g g (lambda (hehe kkk) (hehe x k kkk)) kk))
          k0 k1))
     k0
     k1)))
#; 
(why-cps-cps almost-length-cps (lambda (f) ;; not work yet, don't know why, 'll figure it out.
                                 (f '(1 2 3) (empty-k)))
             (empty-k))
;; how to use why-cps-cps, Havn't figured it out.





; =========================== real Brainteaser ==============================
(define cps
  (lambda (exp)
    (letrec ([id (lambda (x) x)]
             [ctx0 (lambda (x) `(kkk ,x))]
             [fv (let ([n -1])
                   (lambda ()
                     (set! n (+ n 1))
                     (string->symbol
                      (string-append "v"
                                     (number->string n)))))]
             [cps1 (lambda (exp ctx)
                     (pmatch exp
                       [`,x (guard (symbol? x)) (ctx x)]
                       [`(if ,test ,conseq ,alt)
                        (cps1 test
                              (lambda (t)
                                (cond
                                  [(memq ctx `(id ctx0))
                                   `(if ,t ,(cps1 conseq ctx)
                                        ,(cps1 alt ctx))]
                                  [else (let ([v (fv)])
                                          `(let ([k (lambda (,v)
                                                      ,(cps1 v ctx))])
                                             (if ,t ,(cps1 conseq ctx0)
                                                 ,(cps1 alt ctx0))))])))]
                       [`(lambda (,x) ,body)
                        (ctx `(lambda (,x kkk)
                                ,(cps1 body ctx0)))]
                       [`(lambda (,x ,y) ,body)
                        (ctx `(lambda (,x ,y kkk)
                                ,(cps1 body ctx0)))]
                       [`(,rator ,rand)
                        (cps1 rand
                              (lambda (d)
                                (cps1 rator
                                      (lambda (a)
                                        (cond
                                          [(eq? ctx ctx0) `(,a ,d kkk)]
                                          [else (let ([v (fv)])
                                                  `(,a ,d
                                                       (lambda (,v)
                                                         ,(cps1 v ctx))))])))))]
                       [`(,rator ,rand1 ,rand2)
                        (cps1 rand1
                              (lambda (r1)
                                (cps1 rand2
                                      (lambda (r2)
                                        (cps1 rator
                                              (lambda (a)
                                                (cond
                                                  [(eq? ctx ctx0) `(,a ,r1 ,r2 kkk)]
                                                  [else (let ([v (fv)])
                                                          `(,a ,r1 ,r2
                                                               (lambda (,v)
                                                                 ,(cps1 v ctx))))])))))))]))])
      (cps1 exp id))))
#;(cps '(lambda (f)
          ((lambda (g)
             (f (lambda (x) ((g g) x))))
           (lambda (g)
             (f (lambda (x) ((g g) x)))))))
; ==>
#;(lambda (f k)
    ((lambda (g k) (f (lambda (x k) (g g (lambda (v1) (v1 x k)))) k))
     (lambda (g k) (f (lambda (x k) (g g (lambda (v0) (v0 x k)))) k))
     k))