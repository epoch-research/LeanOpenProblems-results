import FormalConjectures.Util.ProblemImports

theorem ltest (n : Nat) (h : n > 13) : n > 0 := by omega
#print axioms ltest

theorem ltest2 (x : Int) (h : x > 1) : x + x > 0 := by linarith
#print axioms ltest2
