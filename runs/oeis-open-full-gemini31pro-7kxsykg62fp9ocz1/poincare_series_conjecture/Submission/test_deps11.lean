import Submission.Spec

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  -- Can we prove False?
  -- Wait, type_of% @poincare_series_conjecture is the Prop `A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices`.
  -- Is there some property of PQS that makes this always false?
  -- No, because poincare_series_genus2_odd_unimodular_lattices is an axiom, so it can be ANY element of PQS.
  -- Wait! Unless PQS is empty? No, PowerSeries ℚ is a ring, so it has 0, 1, etc.
  sorry
