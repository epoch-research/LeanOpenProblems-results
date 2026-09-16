import Submission.Spec
open Nat

#eval! (A003162.b (3 * 5 ^ 1) : ℤ) ≡ (A003162.b (3 * 5 ^ 0) : ℤ) [ZMOD (5 : ℤ) ^ (3 * 1)]
