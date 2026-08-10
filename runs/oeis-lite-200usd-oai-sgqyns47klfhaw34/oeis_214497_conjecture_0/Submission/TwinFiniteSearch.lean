import FormalConjectures.Util.ProblemImports
open Nat

def TwinCenter2 (m : ℕ) : Prop := Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)

example : {m : ℕ | TwinCenter2 m}.Finite := by
  exact?

example : ¬ {m : ℕ | TwinCenter2 m}.Infinite := by
  exact?

example : Set.Finite {m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} := by
  apply?
