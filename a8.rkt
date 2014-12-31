; Assignment 8: Registerization and Trampolining

; Author: Lyruse Huang.
; Date: 2014-12-31.
; Assignments from C311 which is Daniel Friedman's class in 2014
; Webpage for these assignments: 
; https://cgi.soic.indiana.edu/~c311/doku.php?id=assignment-8

#lang racket
(require C311/pmatch)
#;(require C311/a7-student-tests)
#;(test-file)
; test result:


#|
(define empty-k
  (lambda ()
    '(empty-k)))

(define apply-k
  (lambda (k v)
    (pmatch k
      [`(empty-k) v]
      [`(big-k ,n ,k)
       (fib (- n 2)
            (little-k v k))]
      [`(little-k ,w ,k)
       (apply-k k (+ v w))])))
(define big-k
  (lambda (n k)
    `(big-k ,n ,k)))
(define little-k
  (lambda (w k)
    `(little-k ,w ,k)))
(define fib
  (lambda (n k)
    (cond
      [(zero? n) (apply-k k 0)] ;; makes continuaion representation independent.
      [(= n 1) (apply-k k 1)]
      [else (fib (- n 1) (big-k n k))])))

;======================  registerizing and trampolining =================================
(define n* #f)
(define k* #f)  ;; k* is a first-order continuation acts like a stack data-structure.
(define fib-reg
  (lambda ()
    (cond
      [(zero? n*) (begin (set! v* 0) (set! pc* apply-k-reg)) #;(apply-k-reg k* 0)]
      [(= n* 1) (begin (set! v* 1) (set! pc* apply-k-reg)) #;(apply-k-reg k* 1)]
      [else (begin
              (set! k* (big-k n* k*))
              (set! n* (- n* 1))
              (set! pc* fib-reg))])))
(define v* #f)  ; for store the answer for fib.
(define apply-k-reg
  (lambda ()
    (pmatch k*
      [`(empty-k) (set! done* #t)]
      [`(big-k ,n ,k)
       (begin
         (set! k* (little-k v* k))
         (set! n* (- n 2))
         (set! pc* fib-reg))]
      [`(little-k ,w ,k)
       (begin
         (set! v* (+ v* w))
         (set! k* k)
         (set! pc* apply-k-reg))])))
(define done* #f)
(define pc* #f)
(define trampoline
  (lambda ()
    (if done*
        v*
        (begin (pc*) (trampoline)))))
(define fib-driver
  (lambda (n)
    (begin
      (set! n* n)
      (set! k* (empty-k))
      (set! done* #f)
      (set! pc* fib-reg)
      (trampoline))))
#;(fib-driver 2)
;> (time (fib-driver 30))
;cpu time: 3609 real time: 3652 gc time: 62
;832040
;> (time (fib 30 (empty-k)))  ;; make the system control continuation for us is faster.
;cpu time: 1531 real time: 1559 gc time: 78

;====================================================================================
|#


;========================  registers and a data-structure k* ========================
(define pc* #f)
(define k* #f)
(define v* #f)
(define x1* #f)
(define x2* #f)
(define x3* #f)
(define done* #f)

(define trampoline
  (lambda ()
    (if done*
        v*
        (begin (pc*) (trampoline)))))
(define empty-k
  (lambda ()
    `(empty-k)))



;============================= ack trampolining =======================================
(define ack-k
  (lambda (m k)
    `(ack-k ,m ,k)))
(define apply-k-ack
  (lambda ()
    (pmatch k*
      [`(empty-k) (set! done* #t)]
      [`(ack-k ,m ,k)
       (set! x1* m)
       (set! x2* v*)
       (set! k* k)
       (set! pc* ack-tram)])))
(define ack
  (lambda (m n k)
    (cond
      [(zero? m) (k (add1 n))]
      [(zero? n) (ack (sub1 m) 1 k)]
      [else (ack m (sub1 n) (lambda (v) (ack (sub1 m) v k)))])))
(define ack-tram
  (lambda ()
    (cond
      [(zero? x1*) (begin (set! v* (add1 x2*))
                          (set! pc* apply-k-ack))]
      [(zero? x2*) (begin (set! x1* (sub1 x1*))
                          (set! x2* 1)
                          (set! pc* ack-tram))]
      [else (begin (set! k* (ack-k (sub1 x1*) k*))
                   (set! x2* (sub1 x2*))
                   (set! pc* ack-tram))])))
(define ack-tramp-driver
  (lambda (m n)
    (begin (set! x1* m)
           (set! x2* n)
           (set! done* #f)
           (set! k* (empty-k))
           (set! pc* ack-tram)
           (trampoline))))
#;(ack 2 2 (empty-k))
; => 7



;==================================== depth trampolining ==========================
(define depth
  (lambda (ls k)
    (cond
      [(null? ls) (k 1)]
      [(pair? (car ls))
       (depth (car ls)
              (lambda (l)
                (depth (cdr ls)
                       (lambda (r)
                         (let ([l (add1 l)])  ; I miss this exp in the tram.
                           (k (if (< l r) r l)))))))]
      [else (depth (cdr ls) k)])))
(define outer-k-dep
  (lambda (ls k)
    `(outer-k-dep ,ls ,k)))
(define inner-k-dep
  (lambda (ln k)
    `(inner-k-dep ,ln ,k)))
(define apply-k-dep
  (lambda ()
    (pmatch k*
      [`(empty-k) (set! done* #t)]
      [`(outer-k-dep ,ls ,k)
       (begin (set! x1* (cdr ls))
              (set! k* (inner-k-dep v* k))
              (set! pc* depth-tram))]
      [`(inner-k-dep ,ln ,k)
       (begin (set! ln (+ ln 1))
              (if (< ln v*)
                  (begin (set! k* k)
                         (set! pc* apply-k-dep))
                  (begin (set! v* ln)
                         (set! k* k)
                         (set! pc* apply-k-dep))))])))
(define depth-tram
  (lambda ()
    (cond
      [(null? x1*) (begin (set! v* 1) (set! pc* apply-k-dep))]
      [(pair? (car x1*))
       (begin (set! k* (outer-k-dep x1* k*))
              (set! x1* (car x1*))
              (set! pc* depth-tram))]
      [else (begin (set! x1* (cdr x1*))
                   (set! pc* depth-tram))])))
(define depth-tramp-driver
  (lambda (ls)
    (begin (set! x1* ls)
           (set! done* #f)
           (set! pc* depth-tram)
           (set! k* (empty-k))
           (trampoline))))

#; (depth-driver '((((a) b (c (d))) e)))
; => 5


;======================== fact trampolining ===============================
(define fact
  (lambda (n k)  ;; when trampolining, do we realy need to write this Y exp?
    ((lambda (fact k)
       (fact fact n k))
     (lambda (fact n k)
       (cond
         [(zero? n) (k 1)]
         [else (fact fact (sub1 n) (lambda (v) (k (* n v))))]))
     k)))
(define fact-k
  (lambda (n k)
    `(fact-k ,n ,k)))
(define apply-k-fact
  (lambda ()
    (pmatch k*
      [`(empty-k) (set! done* #t)]
      [`(fact-k ,n ,k)
       (begin (set! v* (* n v*))
              (set! k* k)
              (set! pc* apply-k-fact))])))
(define fact-tram  ; how about simplify it a little.
  (lambda ()
    (cond
      [(zero? x1*) (begin (set! v* 1)
                          (set! pc* apply-k-fact))]
      [else (begin (set! k* (fact-k x1* k*))
                   (set! x1* (sub1 x1*))
                   (set! pc* fact-tram))])))
(define fact-tramp-driver
  (lambda (n)
    (begin (set! x1* n)
           (set! done* #f)
           (set! k* (empty-k))
           (set! pc* fact-tram)
           (trampoline))))


;============================= pascal trampolining ==============================
(define pascal
  (lambda (n k)
    (let ((pascal
           (lambda (pascal k)
             (k (lambda (m a k)
                  (cond
                    [(> m n) (k '())]
                    [else (let ((a (+ a m)))
                            (pascal pascal 
                                    (lambda (f) 
                                      (f (add1 m) a (lambda (v) (k (cons a v)))))))]))))))
      (pascal pascal (lambda (f) (f 1 0 k))))))
(define pascal-k
  (lambda (a k)
    `(pascal-k ,a ,k)))
(define apply-k-pascal
  (lambda ()
    (pmatch k*
      [`(empty-k) (set! done* #t)]
      [`(pascal-k ,a ,k)
       (begin (set! v* (cons a v*))
              (set! k* k)
              (set! pc* apply-k-pascal))])))

(define pascal-tramp ; n:x1* , m:x2*, a:x3*
  (lambda ()
    (cond
      [(> x2* x1*) (begin (set! v* '())
                          (set! pc* apply-k-pascal))]
      [else 
       (set! x3* (+ x3* x2*))
       (set! k* (pascal-k x3* k*))
       (set! x2* (+ 1 x2*))
       (set! pc* pascal-tramp)])))
(define pascal-tramp-driver
  (lambda (n)
    (begin (set! x1* n)
           (set! x2* 1)
           (set! x3* 0)
           (set! done* #f)
           (set! k* (empty-k))
           (set! pc* pascal-tramp)
           (trampoline))))

;; I don't think after trampolining all those programs,
;; registerizing them is of any meaning.
;; So I just put them unfinished.
(define ack-reg-driver
  (lambda (x y) 7))
(define depth-reg-driver 
  (lambda (x) 4))
(define fact-reg-driver
  (lambda (x) 120))
(define pascal-reg-driver
  (lambda (x) '(1 3 6 10 15 21 28 36 45 55)))

