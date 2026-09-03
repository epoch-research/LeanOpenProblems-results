import Submission.PolylogSpectrumInterval

/-! Type checks and permitted-axiom audit for the restricted exponent interval. -/

open Nat Filter
namespace Erdos821

example (κ : ℝ) (hκ : 1<κ) (hκb : κ≤2000001/963433) :
    sSup {γ : ℝ | {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite} = 1-1/κ :=
  polylog_critical_exponent_wide_interval κ hκ hκb

example (κ γ : ℝ) (hκ : 1<κ) (hκb : κ≤2000001/963433) (hγ : γ<1-1/κ) :
    {n : ℕ | (gPolylog κ n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_gPolylog_gt_wide_interval κ γ hκ hκb hγ

#print axioms exists_polylog_density_parameters
#print axioms infinite_gPolylog_gt_of_polynomial_count
#print axioms finite_gPolylog_exceedance
#print axioms polylog_critical_exponent_of_polynomial_count
#print axioms wide_block_eventual_polynomial_count
#print axioms polylog_critical_exponent_wide_interval
#print axioms infinite_gPolylog_gt_wide_interval

end Erdos821
