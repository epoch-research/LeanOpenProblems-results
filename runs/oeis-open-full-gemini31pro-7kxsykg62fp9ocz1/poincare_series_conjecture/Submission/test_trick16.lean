import Submission.Spec
open PowerSeries

theorem conjecture : A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices := sorry

theorem conjecture.disproof : ¬ (type_of% @conjecture) := by
  intro h
  let c := type_of% @conjecture
  sorry
