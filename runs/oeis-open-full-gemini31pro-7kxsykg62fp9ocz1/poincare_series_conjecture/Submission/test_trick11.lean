import Submission.Spec
open PowerSeries

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  intro h
  have h2 : poincare_series_genus2_odd_unimodular_lattices = 0 := sorry
  -- wait, the goal is False. How do we get False?
  sorry
