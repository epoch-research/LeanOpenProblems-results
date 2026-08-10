import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.valuation
#check Padic.norm_eq_zpow_neg_valuation
#check Padic.norm_p
#check Padic.norm_p_pow
#check Padic.norm_int
#check Padic.norm_rat
#check Padic.norm_le_one_iff_val_nonneg
#check PadicInt.subring
#check PadicInt.mem_subring_iff
#check PadicInt.coeToPadic
#check PadicInt.toPadic
#check PadicInt.norm_le_one
#check Padic.tendsto_pow_atTop_nhds_zero
#check Padic.summable
#check Padic.hasSum
#check NormedAddCommGroup.tsum_eq_zero_of_not_summable
#check Summable.hasSum
#check tsum_eq_zero_of_not_summable
