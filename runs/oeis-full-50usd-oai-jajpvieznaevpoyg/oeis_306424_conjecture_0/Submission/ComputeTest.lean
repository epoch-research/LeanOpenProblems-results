import FormalConjectures.Util.ProblemImports

open List Finset Nat

example : (Nat.digits 4 44) = [0,3,2] := by
  norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]

example : ¬ (((Nat.digits 4 44).toFinset.card) ≤ 2) := by
  norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]

example : ((Nat.digits 3 43).toFinset.card) ≤ 2 := by
  norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]
