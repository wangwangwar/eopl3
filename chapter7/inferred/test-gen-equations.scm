(module test-gen-equations (lib "eopl.ss" "eopl")
        
        (require "inferrer.scm")
        (require "gen-equations.scm")
        (require "lang.scm")
        
        (define exp1
            (zero?-exp (const-exp 3)))

        (define exp2
          (diff-exp exp1 (const-exp 3)))
        
        (define exp3
          (diff-exp (const-exp 2) (const-exp 3)))

        (define exp4
          (if-exp (zero?-exp (const-exp 3))  
                  (const-exp 2)
                  (zero?-exp (const-exp 0))))

        (display (type-of-ex7.27 exp4))
        
        )
