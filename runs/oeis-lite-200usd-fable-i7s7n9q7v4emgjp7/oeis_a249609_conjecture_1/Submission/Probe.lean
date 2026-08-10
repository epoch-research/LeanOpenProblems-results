import FormalConjectures.Util.ProblemImports
open Nat List

example : Nat.bits 21 = [true, false, true, false, true] := by decide
example : Nat.bits 21 = [true, false, true, false, true] := by rfl
example : Nat.choose 14 7 = 3432 := by decide
example : (Nat.bits 3432).count true = 6 := by decide
