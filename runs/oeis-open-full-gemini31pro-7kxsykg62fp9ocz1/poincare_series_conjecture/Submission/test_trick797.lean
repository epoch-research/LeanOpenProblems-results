import Submission.Spec
open PowerSeries

theorem test : ∃ (x : PQS), x = poincare_series_genus2_odd_unimodular_lattices := by
  exact ⟨poincare_series_genus2_odd_unimodular_lattices, rfl⟩
