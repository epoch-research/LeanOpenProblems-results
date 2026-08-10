import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.norm_le_pow_iff_mem_span_pow
#check Padic.norm_le_pow_iff_mem_span_pow'
#check padicNorm
#check summable_of_norm_bounded_eventually_geometric_of_norm_tendsto_zero
#check summable_of_isLittleO_nat
#check summable_of_norm_bounded
#check CauchySeq_finset_iff_vanishing_norm
#check NonarchimedeanAddGroup.summable_iff_vanishing_norm
#check NormedAddCommGroup.summable_iff_vanishing_norm
#check NNReal.summable_geometric
#check Padic.norm_rat
#check Padic.valuation_natCast
#check Padic.norm_int
#check Padic.nnnorm_eq_zpow_neg_valuation
#check padicValNat_factorial_lt_of_ne_zero
#check sub_one_mul_padicValNat_factorial
example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  -- exact?
  sorry
