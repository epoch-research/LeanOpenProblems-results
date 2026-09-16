import Submission.Spec
open Nat

theorem div4 : (Nat.divisors 4).sort (· ≤ ·) = [1, 2, 4] := by rfl
