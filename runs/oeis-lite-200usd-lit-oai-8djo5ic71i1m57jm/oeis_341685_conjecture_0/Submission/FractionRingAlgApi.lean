import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Algebra.IsAlgebraic.finrank_of_isFractionRing
#check Algebra.IsAlgebraic.rank_of_isFractionRing
#check Algebra.IsAlgebraic.lift_rank_of_isFractionRing
#check Algebra.IsAlgebraic.rank_fractionRing
#print Algebra.IsAlgebraic.rank_fractionRing
#check PadicInt.isFractionRing (p:=3)
#check IsFractionRing.liftAlgebra
#check IsLocalization.isAlgebraic
#check isAlgebraic_of_isFractionRing
#print isAlgebraic_of_isFractionRing
