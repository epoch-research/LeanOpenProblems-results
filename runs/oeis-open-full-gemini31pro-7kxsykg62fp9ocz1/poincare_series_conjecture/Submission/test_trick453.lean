import Submission.Spec
open PowerSeries

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  intro h
  have h_eq : (0 : PQS) = 1 := by
    -- wait, PQS is PowerSeries ℚ.
    -- Could there be an error in the definition of A097913.generating_function?
    -- `let den : PQS := (1 - X) * (1 - X ^ 8) * (1 - X ^ 12) * (1 - X ^ 24)`
    -- `num * den⁻¹`
    -- What if `den` is not invertible?
    -- The constant term of `den` is `1 * 1 * 1 * 1 = 1`, which is invertible.
    -- Wait, `den⁻¹` requires `den` to be a unit. Is `Inv` defined for `PQS`?
    sorry
  sorry
