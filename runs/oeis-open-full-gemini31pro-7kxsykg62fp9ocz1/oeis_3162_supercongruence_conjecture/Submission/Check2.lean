import Submission.Spec
open Nat

def check_val : Bool :=
  let lhs : ℤ := A003162.b (1 * 5 ^ 1)
  let rhs : ℤ := A003162.b (1 * 5 ^ 0)
  let m : ℤ := (5 : ℤ) ^ (3 * 1)
  lhs ≡ rhs [ZMOD m]

#eval check_val
