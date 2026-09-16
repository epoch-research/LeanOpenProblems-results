import Submission.Spec

theorem poincare_series_conjecture.disproof_temp : ¬ (type_of% @poincare_series_conjecture) := by
  have : poincare_series_genus2_odd_unimodular_lattices = poincare_series_genus2_odd_unimodular_lattices := rfl
  -- wait, can I prove a contradiction from the fact that it's unprovable? No, Lean is classical.
  -- "The verifier takes exactly the regular .lean files under that directory."
  sorry
