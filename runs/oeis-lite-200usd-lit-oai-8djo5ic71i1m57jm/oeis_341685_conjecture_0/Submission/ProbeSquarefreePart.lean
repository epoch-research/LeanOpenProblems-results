import FormalConjectures.Util.ProblemImports
open Nat
example : False := by
  have h := Nat.squarefreePart_of_isSquare (n := 0) (by use 0; simp)
  norm_num [Nat.squarefreePart_zero] at h
example : False := by
  have h := Nat.squarefreePart_mul_squarePart 0
  norm_num [Nat.squarefreePart_zero, Nat.squarePart_zero] at h
