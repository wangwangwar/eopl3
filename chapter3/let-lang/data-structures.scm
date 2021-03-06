(module data-structures (lib "eopl.ss" "eopl")

  ;; data structures for let-lang.

  (provide (all-defined-out))               ; too many things to list

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.

  (define-datatype expval expval?
    (num-val
      (value number?))
    (emptylist-val)
    (cons-val
      (car expval?)
      (cdr expval?))
    (cond-val
      (predicates (list-of expval?))
      (values (list-of expval?)))
    )

;;; extractors:

;; expval->num : ExpVal -> Int
;; Page: 70
(define expval->num
  (lambda (v)
    (cases expval v
           (num-val (num) num)
           (else (expval-extractor-error 'num v)))))

(define expval->cons
  (lambda (v)
    (cases expval v
           (cons-val (car cdr)
                     (cons car cdr))
           (else (expval-extractor-error 'cons v)))))

(define expval->null?
  (lambda (v)
    (cases expval v
           (emptylist-val () (num-val 1))
           (else (num-val 0)))))

(define expval->car
  (lambda (v)
    (cases expval v
           (cons-val (car cdr) car)
           (else (expval-extractor-error 'car v)))))

(define expval->cdr
  (lambda (v)
    (cases expval v
           (cons-val (car cdr) cdr)
           (else (expval-extractor-error 'cdr v)))))

(define list-val
  (lambda (args)
    (if (null? args)
      (emptylist-val)
      (cons-val (car args)
                (list-val (cdr args))))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

;;;;;;;;;;;;;;;; environment structures ;;;;;;;;;;;;;;;;

;; example of a data type built without define-datatype

(define empty-env-record
  (lambda () 
    '()))

(define extended-env-record
  (lambda (sym val old-env)
    (cons (list sym val) old-env)))

(define empty-env-record? null?)

(define environment?
  (lambda (x)
    (or (empty-env-record? x)
        (and (pair? x)
             (symbol? (car (car x)))
             (expval? (cadr (car x)))
             (environment? (cdr x))))))

(define extended-env-record->sym
  (lambda (r)
    (car (car r))))

(define extended-env-record->val
  (lambda (r)
    (cadr (car r))))

(define extended-env-record->old-env
  (lambda (r)
    (cdr r)))

)
