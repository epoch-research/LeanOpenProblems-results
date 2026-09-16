import Mathlib
import Submission.Spec
open Nat

def check_val (n k p : ℕ) : Bool :=
  let lhs : ℤ := A003162.b (n * p ^ k)
  let rhs : ℤ := A003162.b (n * p ^ (k - 1))
  let m : ℤ := (p : ℤ) ^ (3 * k)
  lhs ≡ rhs [ZMOD m]

#eval check_val 1 1 5
#eval A003162.b (1 * 5^1)
#eval A003162.b (1 * 5^0)
