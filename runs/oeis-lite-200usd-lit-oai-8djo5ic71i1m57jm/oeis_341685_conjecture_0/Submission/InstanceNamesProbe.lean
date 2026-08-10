import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.instRing
#check Padic.instField
#check DivisionRing.toRatAlgebra
#check Rat.instAlgebraRat
#check Padic.instAlgebraRat
#check Padic.instCommRing
#check Padic.instDivisionRing
#check Padic.instCommSemiring
#print instances Algebra ℚ (Padic 3)
#print instances Ring (Padic 3)
