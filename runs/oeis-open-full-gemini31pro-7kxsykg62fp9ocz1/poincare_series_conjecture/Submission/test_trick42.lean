import Submission.Spec
open PowerSeries

theorem conjecture : A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices := sorry

theorem conjecture.disproof : ¬ (type_of% @conjecture) := by
  have H : type_of% @conjecture := by
    -- can we just use axiom?
    sorry
  sorry
