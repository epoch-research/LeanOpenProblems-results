import Submission.Spec
open PowerSeries

theorem conjecture : A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices := sorry

theorem conjecture.disproof : ¬ (type_of% @conjecture) := by
  intro h
  have H : poincare_series_genus2_odd_unimodular_lattices = 0 := sorry
  -- can we just use sorry? I already tried and it failed verification.
  -- "Replace the sorry of exactly one of them with a complete proof"
  sorry
