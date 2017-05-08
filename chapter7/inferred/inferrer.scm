(module inferrer  (lib "eopl.ss" "eopl")

  (require "drscheme-init.scm")
  (require "lang.scm")
  (require "data-structures.scm")
  (require "unifier.scm")
  (require "substitutions.scm")
  (require "gen-equations.scm")
  (require "tenv.scm")

  (provide type-of-program type-of)

  ;;;;;;;;;;;;;;;; The Type Checker ;;;;;;;;;;;;;;;;

  ;; we'll be thinking of the type of an expression as pair consisting
  ;; of a type (possibly with some type variables in it) and a
  ;; substitution that tells us how to interpret those type variables.

  ;; Answer = Type * Subst
  ;; type-of: Exp * Tenv * Subst  -> Answer

  (define-datatype answer answer?
    (an-answer                       
      (type type?)
      (subst substitution?)))

  ;; type-of-program : Program -> Type
  ;; Page: 267
  (define type-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1)
          (cases answer 
                 (begin 
                   (initialize-subst!-ex7.21)
                   (type-of-ex7.27 exp1 (init-tenv)))
            (an-answer (ty subst)
                       ;(eopl:printf "type-of-program\nty: ~s\nsubst: ~s\n" ty subst)
              (apply-subst-to-type ty subst)))))))

  ;; type-of : Exp * Tenv * Subst -> Type
  ;; Page: 267--270
  (define type-of
    (lambda (exp tenv subst)
      (cases expression exp
        
        (const-exp (num) 
          (eopl:printf "*type-of const-exp*\n  exp1: ~s\n  type1: int-type\n  subst1: ~s\n\n" num subst)
          (an-answer (int-type) subst))
      
        (zero?-exp (exp1)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (type1 subst1)
              (eopl:printf "*type-of zero?-exp*\n  exp1: ~s\n  type1: ~s\n  subst1: ~s\n\n" exp1 type1 subst1)
              (let ((subst2 (unifier type1 (int-type) subst1 exp)))
                (an-answer (bool-type) subst2)))))

        (diff-exp (exp1 exp2)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (type1 subst1)
              (eopl:printf "*type-of diff-exp*\n  exp1: ~s\n  type1: ~s\n  subst1: ~s\n\n" exp1 type1 subst1)
              (let ((subst1 (unifier type1 (int-type) subst1 exp1)))
                (cases answer (type-of exp2 tenv subst1)
                  (an-answer (type2 subst2)
                    (let ((subst2
                            (unifier type2 (int-type) subst2 exp2)))
                      (an-answer (int-type) subst2))))))))

        (if-exp (exp1 exp2 exp3)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (ty1 subst)
              (let ((subst (unifier ty1 (bool-type) subst
                             exp1)))
                (cases answer (type-of exp2 tenv subst)
                  (an-answer (ty2 subst)
                    (cases answer (type-of exp3 tenv subst)
                      (an-answer (ty3 subst)
                        (eopl:printf "*type-of if-exp*\n  exp3: ~s\n  type3: ~s\n  subst: ~s\n\n" exp3 ty3 subst)
                        (let ((subst (unifier ty2 ty3 subst exp)))
                          (an-answer ty2 subst))))))))))

        (var-exp (var) 
          (let ((var-type (apply-tenv tenv var)))
            (eopl:printf "*type-of var-exp*\n  var: ~s\n  type: ~s\n  subst: ~s\n\n" var var-type subst)
            (an-answer var-type subst)))

        (let-exp (var exp1 body)
          (eopl:printf "*type-of let-exp*\n  var: ~s\n  exp1: ~s\n  body: ~s\n\n" var exp1 body)
          (cases answer (type-of exp1 tenv subst)
            (an-answer (rhs-type subst)
              (type-of body
                (extend-tenv var rhs-type tenv)
                subst))))

        (proc-exp (var otype body)
          (let ((arg-type (otype->type otype)))
            (eopl:printf "*type-of proc-exp*\n  var: ~s\n  otype: ~s\n  body: ~s\n\n" var otype body)
            (cases answer (type-of body
                            (extend-tenv var arg-type tenv)
                            subst)
              (an-answer (result-type subst)
                (an-answer
                  (proc-type arg-type result-type)
                  subst)))))

        (call-exp (rator rand)
          (let ((result-type (fresh-tvar-type)))
            (cases answer (type-of rator tenv subst)
              (an-answer (rator-type subst)
                (cases answer (type-of rand tenv subst)
                  (an-answer (rand-type subst)
                    (eopl:printf "*type-of call-exp*\n  rator-type: ~s\n  rand-type: ~s\n  subst: ~s\n\n" 
                                 rator-type rand-type subst)
                    (let ((subst
                            (unifier rator-type
                              (proc-type rand-type result-type)
                              subst
                              exp)))
                      (an-answer result-type subst))))))))

        (letrec-exp (proc-result-otype proc-name 
                      bvar proc-arg-otype 
                      proc-body
                      letrec-body)
          (let ((proc-result-type
                  (otype->type proc-result-otype)) 
                (proc-arg-type
                  (otype->type proc-arg-otype)))
            (let ((tenv-for-letrec-body
                    (extend-tenv 
                      proc-name
                      (proc-type proc-arg-type proc-result-type)
                      tenv)))
              (cases answer (type-of proc-body
                              (extend-tenv
                                bvar proc-arg-type tenv-for-letrec-body)
                              subst)
                (an-answer (proc-body-type subst)
                  (eopl:printf "*type-of letrec-exp*\n  proc-body-type: ~s\n  subst: ~s\n\n" proc-body-type subst)
                  (let ((subst 
                          (unifier proc-body-type proc-result-type subst
                            proc-body))) 
                    (type-of letrec-body
                      tenv-for-letrec-body
                      subst)))))))
        
        )))

  ;; Exercise 7.27 [**] Rewrite the inferencer so that it works in two phases. 
  ;; In the ﬁrst phase it should generate a set of equations, and in the second 
  ;; phase, it should repeat- edly call unify to solve them.
  ;; 
  (define type-of-ex7.27
    (lambda (exp tenv)
      (initialize-subst!-ex7.21)
      (let* ((pair (gen-equations exp tenv))
             (target-type (car pair))
             (equations (cdr pair))
             (subst (unifier-ex7.27 equations (empty-subst))))
        (an-answer target-type (get-subst-ex7.21)))))

    ;;;;;;;;;;;;;;;; type environments ;;;;;;;;;;;;;;;;
    
  ;; why are these separated?

  )
