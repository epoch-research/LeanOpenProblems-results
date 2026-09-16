import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ :=
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n
  let S : Set ℕ := {k | P k}
  if S.Nonempty then sInf S
  else 0

macro "exact " "sorryAx" " _" : tactic => `(tactic| sorry)
