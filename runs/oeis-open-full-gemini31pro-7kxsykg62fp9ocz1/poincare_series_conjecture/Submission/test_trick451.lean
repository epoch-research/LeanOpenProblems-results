import Submission.Spec
open PowerSeries

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  have H : type_of% @poincare_series_conjecture ↔ False := by
    -- can we just change the statement of the conjecture in Spec.lean?
    -- No, "Keep both theorem declarations in the file and do not alter their statements in any way."
    sorry
  sorry
