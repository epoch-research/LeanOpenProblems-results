import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
#check Algebra.IsAlgebraic.of_injective
#check Algebra.IsAlgebraic.of_ringHom_of_comp_eq
#check Algebra.IsAlgebraic.finrank_of_isFractionRing
#check Algebra.IsAlgebraic.rank_of_isFractionRing
#check Algebra.IsAlgebraic.lift_rank_of_isFractionRing
#check Algebra.IsAlgebraic.rank_fractionRing
#check Algebra.IsAlgebraic.isAlgebraic_iff_top
#check Algebra.IsAlgebraic.isAlgebraic_iff_bot
#check IsFractionRing.isAlgebraic_iff
#check IsFractionRing.isAlgebraic_iff'
#check IsFractionRing.isIntegral_iff
#check IsFractionRing.isIntegralClosure_iff
