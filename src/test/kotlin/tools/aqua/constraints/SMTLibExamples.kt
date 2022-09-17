package tools.aqua.constraints.expressions

// Cf. https://smtlib.cs.uiowa.edu/examples.shtml

object SMTLibExamples {

    val example1 = """
        ; Basic Boolean example
        (set-option :print-success false)
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert (and p (not p))) 
        (check-sat) ; returns 'unsat'
        (exit)    
    """.trimIndent()

    val example2 = """
        ; Integer arithmetic
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (- x y) (+ x (- y) 1)))
        (check-sat)
        ; unsat
        (exit)
    """.trimIndent()

    val example3 = """
        ; Getting values or models
        (set-option :print-success false)
        (set-option :produce-models true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ x (* 2 y)) 20))
        (assert (= (- x y) 2))
        (check-sat)
        ; sat
        ; (get-value (x y))
        ; ((x 8) (y 6))
        (get-model)
        ; ((define-fun x () Int 8)
        ;  (define-fun y () Int 6)
        ; )
        (exit)        
    """.trimIndent()

    val example4 = """
        (set-logic QF_UFLIA)
        (set-option :produce-models true)
        (declare-fun x (Int) Int)  (declare-fun y (Int) Int)
        (declare-fun t (Int) Int)
        (assert (= (t 0) (x 0)))
        (assert (= (y 1) (t 0)))
        (assert (= (x 1) (y 1)))

        (assert (not 
          (and (= (x 1) (y 0)) 
               (= (y 1) (x 0)))))
        (check-sat)
        ; (get-value ((x 0) (y 0) (x 1) (y 1)))
        ; possible returned valuation:
        ; (((x 0) (- 1)) ((y 0) 2) ((x 1) (- 1)) ((y 1) (- 1)))
        (get-model)
        ; possible returned model:
        ; (
        ;  (define-fun x ((_ufmt_1 Int)) Int (- 1))
        ;  (define-fun y ((_ufmt_1 Int)) Int (ite (= _ufmt_1 1) (- 1) 2))
        ;  (define-fun t ((_ufmt_1 Int)) Int (- 1))
        ; )
        (exit)        
    """.trimIndent()

    val example5 = """
        (set-logic QF_BV) 
        (set-option :produce-models true)

        (declare-const x_0 (_ BitVec 32))
        (declare-const x_1 (_ BitVec 32))
        (declare-const x_2 (_ BitVec 32))   
        (declare-const y_0 (_ BitVec 32))
        (declare-const y_1 (_ BitVec 32))   
        (assert (= x_1 (bvadd x_0 y_0))) 
        (assert (= y_1 (bvsub x_1 y_0)))
        (assert (= x_2 (bvsub x_1 y_1)))

        (assert (not
          (and (= x_2 y_0)
               (= y_1 x_0))))
        (check-sat)
        ; unsat
        (exit)        
    """.trimIndent()

    val example6 = """
        ; Using scopes to explore multiple problems
        (set-option :print-success false)
        (set-logic QF_LIA)
        (declare-const x Int) (declare-const y Int)
        (assert (= (+ x (* 2 y)) 20))
        (push 1)
          (assert (= (- x y) 2))
          (check-sat)
          ; sat
        (pop 1)
        (push 1)
          (assert (= (- x y) 3))
          (check-sat)
          ; unsat
        (pop 1)
        (exit)        
    """.trimIndent()
}
