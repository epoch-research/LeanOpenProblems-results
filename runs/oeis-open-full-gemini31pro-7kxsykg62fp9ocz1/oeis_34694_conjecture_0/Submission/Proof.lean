import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ModularCases
import Mathlib.Data.Nat.ChineseRemainder

open Nat

-- We want to show there exists n > 1 such that for all k < n, k*n+1 is composite.
-- We will disprove the conjecture.
