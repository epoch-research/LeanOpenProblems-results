import Mathlib

open Nat

lemma test_3 : IsPrimitiveRoot (2 : ZMod 3) (Nat.totient 3) := by
  decide
