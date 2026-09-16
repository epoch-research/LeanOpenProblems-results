import Submission.Spec
open Nat Finset Complex Real Filter Asymptotics ZMod Int

#eval let P_1 : Complex := Finset.prod (range 2) (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I); Int.floor (P_1.im / 2)
