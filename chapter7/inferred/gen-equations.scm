(module gen-equations-ex7.27 (lib "eopl.ss" "eopl")
        
        (require "drscheme-init.scm")
        (require "lang.scm")
        (require "data-structures.scm")
        
        (provide (all-defined-out))
        
        ;; Ex7.27 [**] Rewrite the inferencer so that it works in two phases.
        ;; In the first phase it should generate a set of equations,
        ;; and in the second phase, it should repeatedly call unify to solve them.
        ;;
        ;; gen-equations : Exp -> Current Exp Type
        ;; Page: 272
        
        (define gen-equations
          (lambda (exp)
            (cases expression exp
                   
                   (const-exp (exp) (int-type))
                   
                   (zero?-exp (exp1)
                              (let ((tvar1 (gen-equations exp1))
                                    (tvar2 (fresh-tvar-type)))
                                (extend-equations! tvar1 (int-type))
                                (extend-equations! tvar2 (bool-type))
                                tvar2))
                   
                   (diff-exp (exp1 exp2)
                             (let ((tvar1 (gen-equations exp1))
                                   (tvar2 (gen-equations exp2))
                                   (tvar3 (fresh-tvar-type)))
                               (extend-equations! tvar1 (int-type))
                               (extend-equations! tvar2 (int-type))
                               (extend-equations! tvar3 (int-type))
                               tvar3))
                   
                   (if-exp (exp1 exp2 exp3)
                           (let ((tvar1 (gen-equations exp1))
                                 (tvar2 (gen-equations exp2))
                                 (tvar3 (gen-equations exp3))
                                 (tvar4 (fresh-tvar-type)))
                             (extend-equations! tvar1 (bool-type))
                             (extend-equations! tvar2 tvar3)
                             (extend-equations! tvar2 tvar4)
                             tvar4
                             ))
                   
                   (var-exp (var) (tvar-type var))
                   
                   (let-exp (var exp1 body)
                            (let ((tvar1 (tvar-type var))
                                  (tvar2 (gen-equations exp1))
                                  (tvar3 (gen-equations body)))
                              (extend-equations! tvar1 tvar2)
                              tvar3))
                   
                   (proc-exp (var otype body)
                             (let ((arg-type (otype->type otype))
                                   (tvar-var (tvar-type var))
                                   (tvar-body (gen-equations body)))
                               (extend-equations! tvar-var arg-type)
                               tvar-body))
                   
                   (call-exp (rator rand)
                             (let ((rator-type (gen-equations rator))
                                   (rand-type (gen-equations rand))
                                   (result-type (fresh-tvar-type)))
                               (extend-equations! rator-type
                                                  (proc-type rand-type result-type))
                               result-type))
                   
                   (letrec-exp (proc-result-otype
                                proc-name
                                bvar
                                proc-arg-otype
                                proc-body
                                letrec-body)
                               (let ((proc-result-type
                                      (otype->type proc-result-otype))
                                     (proc-arg-type
                                      (otype->type proc-arg-otype))
                                     (tvar-proc-name (tvar-type proc-name))
                                     (tvar-bvar (tvar-type bvar))
                                     (tvar-proc-body (gen-equations proc-body))
                                     (tvar-letrec-body (gen-equations letrec-body)))
                                 
                                 (extend-equations! tvar-proc-name
                                                    (proc-type proc-arg-type proc-result-type))
                                 (extend-equations! tvar-bvar proc-arg-type)
                                 (extend-equations! tvar-proc-body proc-result-type)
                                 tvar-letrec-body))
                   )))
        
        ;; fresh-tvar-type : () -> Type
        ;; Page: 265
        (define fresh-tvar-type
          (let ((sn 0))
            (lambda ()
              (set! sn (+ sn 1))
              (tvar-type sn))))
        
        ;; otype->type : OptionalType -> Type
        ;; Page: 265
        (define otype->type
          (lambda (otype)
            (cases optional-type otype
                   (no-type () (fresh-tvar-type))
                   (a-type (ty) ty))))

        ;;;;; Exp-Tvar List
        
        (define empty-exp-tvar-list
          (lambda () '()))
        
        (define the-exp-tvar-list #f)
        
        (define get-exp-tvar-list
          (lambda () the-exp-tvar-list))
        
        (define initialize-exp-tvar-list!
          (lambda () (set! the-exp-tvar-list (empty-exp-tvar-list))))
        
        (define extend-exp-tvar-list!
          (lambda (exp tvar)
            (set! the-exp-tvar-list (set-or-concat the-exp-tvar-list exp tvar))
            (get-exp-tvar-list)))
        
        ;;;;; Equation List
        
        (define empty-equations
          (lambda () '()))
        
        (define the-equations #f)
        
        (define get-equations
          (lambda () the-equations))
        
        (define initialize-equations!
          (lambda () (set! the-equations (empty-equations))))
        
        (define extend-equations!
          (lambda (ty1 ty2)
            (set! the-equations (cons (cons ty1 ty2) the-equations))
            (get-equations)))
        
        ;;;;; Helper
        
        (define set-or-concat
          (lambda (lst key value)
            (if (null? lst)
                (list (cons key value))
              (let ((kv (car lst)))
                (if (not (equal? (car kv) key))
                    (cons kv (set-or-concat (cdr lst) key value))
                  (cons (cons key value) (cdr lst)))))))
        
        )
