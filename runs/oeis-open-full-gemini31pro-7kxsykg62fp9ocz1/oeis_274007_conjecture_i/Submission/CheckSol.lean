import Submission.Spec
import Mathlib

def check_sol : Bool :=
  let x := 0
  let y := 3
  let z := 11
  let w := 36
  let P1 (z : ℕ) : ℕ := (z * (3 * z - 1)) / 2
  let P2 (w : ℕ) : ℕ := (w * (3 * w + 1)) / 2
  x^5 + 2 * y^5 + P1 z + P2 w == 2624

#eval check_sol
