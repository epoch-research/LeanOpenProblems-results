import Submission.Spec
open PowerSeries

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  have h1 : poincare_series_genus2_odd_unimodular_lattices = 0 := sorry
  -- what if we use sorry in a have, does #print axioms show sorry?
  sorry
#print axioms poincare_series_conjecture.disproof_temp
