import Submission.Spec
open PowerSeries

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  have H : False := by
    -- wait, PQS is just PowerSeries ℚ.
    -- is there ANY way `A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices` is false, independent of the axiom?
    -- No, because the axiom has NO constraints.
    -- Therefore, this file MUST be proved by proving the original theorem (`poincare_series_conjecture`).
    -- But HOW to prove the original theorem?
    -- The original theorem is `A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices`.
    -- `poincare_series_genus2_odd_unimodular_lattices` is an AXIOM.
    -- So `A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices` asserts that a specific power series equals an unspecified constant.
    -- This is ALSO unprovable.
    -- How is this task possible?!
    sorry
  exact H.elim
