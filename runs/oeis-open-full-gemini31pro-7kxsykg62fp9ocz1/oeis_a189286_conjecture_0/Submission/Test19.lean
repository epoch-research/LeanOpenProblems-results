import Submission.Spec
open Nat

theorem floor_ineq_lemma (rx ry P : ℕ) (hx : rx < P) (hy : ry < P) :
  (3*rx + 3*ry) / P + (3*rx) / P + (2*rx) / P + rx / P + (3*ry) / P + (2*ry) / P + ry / P
  ≤ (6*rx) / P + (6*ry) / P + (rx + ry) / P + (2*rx + 2*ry) / P := by
  sorry
