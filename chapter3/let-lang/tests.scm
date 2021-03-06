(module tests mzscheme
  
  (provide test-list)

  ;;;;;;;;;;;;;;;; tests ;;;;;;;;;;;;;;;;
  
  (define test-list
    '(
  
      ;; simple arithmetic
      (positive-const "11" 11)
      (negative-const "-33" -33)
      (simple-arith-1 "-(44,33)" 11)
  
      ;; nested arithmetic
      (nested-arith-left "-(-(44,33),22)" -11)
      (nested-arith-right "-(55, -(22,11))" 44)
  
      ;; simple variables
      (test-var-1 "x" 10)
      (test-var-2 "-(x,1)" 9)
      (test-var-3 "-(1,x)" -9)
      
      ;; simple unbound variables
      (test-unbound-var-1 "foo" error)
      (test-unbound-var-2 "-(x,foo)" error)
  
      ;; simple conditionals
      (if-true "if zero?(0) then 3 else 4" 3)
      (if-false "if zero?(1) then 3 else 4" 4)
      
      ;; test dynamic typechecking
      (no-bool-to-diff-1 "-(zero?(0),1)" error)
      (no-bool-to-diff-2 "-(1,zero?(0))" error)
      (no-int-to-if "if 1 then 2 else 3" error)

      ;; make sure that the test and both arms get evaluated
      ;; properly. 
      (if-eval-test-true "if zero?(-(11,11)) then 3 else 4" 3)
      (if-eval-test-false "if zero?(-(11, 12)) then 3 else 4" 4)
      
      ;; and make sure the other arm doesn't get evaluated.
      (if-eval-test-true-2 "if zero?(-(11, 11)) then 3 else foo" 3)
      (if-eval-test-false-2 "if zero?(-(11,12)) then foo else 4" 4)

      ;; simple let
      (simple-let-1 "let x = 3 in x" 3)

      ;; make sure the body and rhs get evaluated
      (eval-let-body "let x = 3 in -(x,1)" 2)
      (eval-let-rhs "let x = -(4,1) in -(x,1)" 2)

      ;; check nested let and shadowing
      (simple-nested-let "let x = 3 in let y = 4 in -(x,y)" -1)
      (check-shadowing-in-body "let x = 3 in let x = 4 in x" 4)
      (check-shadowing-in-rhs "let x = 3 in let x = -(x,1) in x" 2)

      ; check minus expression
      (simple-minus "minus(-(minus(5),9))" 14)

      ; check addition expression
      (simple-addition "+(4,9)" 13)

      ; check multiplication expression
      (simple-multiplication "*(4, 9)" 36)

      ; check integer quotient expression
      (simple-integer-quotient "/(4, 9)" 4/9)

      ; check equal?
      (simple-equal? "equal?(1, 1)" 1)

      ; check greater?
      (simple-greater-1-1? "greater?(1, 1)" 0)
      (simple-greater-1-2? "greater?(1, 2)" 0)
      (simple-greater-3-1? "greater?(3, 1)" 1)

      ; check less?
      (simple-less-1-1? "less?(1, 1)" 0)
      (simple-less-1-2? "less?(1, 2)" 1)
      (simple-less-3-1? "less?(3, 1)" 0)

      ; check null? of '(4 (3))
      (test-cons-null? "let x = 4 in null?(cons(4,
                                           cons(cons(-(x, 1),
                                                      emptylist),
                                                 emptylist)))"  
                       0)
      ; check null? of emptylist
      (test-null?-emptylist "null?(emptylist)" 1)

      ; check car of '(4 (3))
      (test-cons-car "let x = 4 in car(cons(4,
                                           cons(cons(-(x, 1),
                                                      emptylist),
                                                 emptylist)))" 
                     4)
      
      ; check cdr of '(4 3)
      (test-cons-cdr "cdr(cons(4, 3))" 3)

      ; check list
      (test-list "car(list(3, 3, 3))" 3)

      ; check cond
      (test-cond-error "cond 3 ==> 3 end" 3)
      (test-cond-valid "cond less?(3,2) ==> 0 greater?(3,2) ==> 3 end" 3)
      ))
  )
