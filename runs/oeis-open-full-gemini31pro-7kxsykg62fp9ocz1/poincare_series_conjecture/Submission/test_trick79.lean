import Submission.Spec
open PowerSeries

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  intro h
  have H : type_of% @poincare_series_conjecture := h
  -- Wait, the task says:
  -- "To disprove it, fill in the `.disproof` theorem's `sorry`. Its proof must not reference the original theorem (which stays `sorry`)."
  -- I just have to prove `poincare_series_conjecture.disproof`?
  -- But I found out earlier that I cannot prove FALSE from an unspecified axiom `c : Nat` being equal to `0`.
  -- Is there some difference here?
  sorry
