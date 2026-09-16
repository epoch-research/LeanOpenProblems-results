import Submission.Spec
open Nat

theorem floor_ineq (x y P : ℕ) :
  (3*x + 3*y) / P + (3*x) / P + (2*x) / P + x / P + (3*y) / P + (2*y) / P + y / P
  ≤ (6*x) / P + (6*y) / P + (x + y) / P + (2*x + 2*y) / P := by
  omega
