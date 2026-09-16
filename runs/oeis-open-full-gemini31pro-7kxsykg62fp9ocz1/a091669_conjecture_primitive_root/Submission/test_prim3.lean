import Mathlib

open Nat

lemma prim_5 : IsPrimitiveRoot (2 : ZMod 5) 4 := by
  constructor
  · decide
  · intro l hl
    -- wait, check if decide works
    sorry
