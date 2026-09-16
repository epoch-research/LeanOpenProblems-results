import Submission.Spec
open PowerSeries

theorem conjecture : A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices := sorry

theorem conjecture.disproof : ¬ (type_of% @conjecture) := by
  -- Can we prove `type_of% @conjecture` is an empty type or something? No, it's a Prop.
  -- Wait, what if we use `sorry` in `A097913` definition? No, we shouldn't modify the file.
  sorry
