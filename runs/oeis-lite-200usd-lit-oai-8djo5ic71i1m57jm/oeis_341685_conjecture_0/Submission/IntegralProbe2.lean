import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check PadicInt
#check PadicInt.mk
#check IsIntegral
#check isIntegral_iff
#check isIntegral_iff_isAlgebraic
#check IsIntegral.isAlgebraic
#check Algebra.algebraMap_mem
#check ValuationSubring.isIntegral
#check IsIntegralClosure
#check integralClosure
#check mem_integralClosure_iff_mem_valuationSubring
#check PadicInt.norm_le_one
#check PadicInt.coe
#check PadicInt.exists_eq
#check PadicInt.coeToSubring
#check PadicInt.eq
#check Subring.isIntegralClosure_top
#check Algebra.IsIntegral
