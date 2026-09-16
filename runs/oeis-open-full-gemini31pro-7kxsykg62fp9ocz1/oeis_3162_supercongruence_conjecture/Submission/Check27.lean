import Mathlib
open Nat
def test (p k : ℕ) (a b : ℤ) : Prop := a ≡ b [ZMOD (p : ℤ) ^ (3 * k)]
#print test
