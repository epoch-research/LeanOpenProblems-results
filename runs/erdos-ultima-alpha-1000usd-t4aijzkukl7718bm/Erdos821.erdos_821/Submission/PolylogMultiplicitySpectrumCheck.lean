import Submission.PolylogMultiplicitySpectrum

/-! Exact-type checks and permitted-axiom audit for the restricted exponent. -/

open Nat Filter
namespace Erdos821

example (γ : ℝ) (hγ : γ<1036568/2000001) :
    {n : ℕ | (gPolylog (2000001/963433) n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_gPolylog_gt_wide_block γ hγ

example (γ : ℝ) (hγ : 1036568/2000001<γ) :
    {n : ℕ | (gPolylog (2000001/963433) n : ℝ) > (n : ℝ)^γ}.Finite :=
  finite_gPolylog_gt_wide_block γ hγ

#print axioms poolWeight_primesBelow_le_log_four
#print axioms eventually_polylog_input_fiber_bound
#print axioms finite_polylog_totient_fiber
#print axioms gPolylog_le_g
#print axioms finite_fiber_card_le_gPolylog
#print axioms eventually_gPolylog_le
#print axioms infinite_gPolylog_gt_wide_block
#print axioms finite_gPolylog_gt_wide_block
#print axioms polylog_critical_exponent_wide_block

end Erdos821
