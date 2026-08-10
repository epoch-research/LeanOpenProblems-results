import FormalConjectures.Util.ProblemImports
open Nat

abbrev GoalAt (n : ℕ) : Prop := ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
abbrev TargetT : Prop := ∀ n : ℕ, n > 0 → GoalAt n

example : TargetT := by
  let rec instGoal (n : ℕ) : Inhabited (GoalAt n) := instGoal n
  letI (n : ℕ) : Inhabited (GoalAt n) := instGoal n
  exact fun n hn => default

example : TargetT := by
  let rec proofGoal (n : ℕ) : GoalAt n := proofGoal n
  exact fun n hn => proofGoal n
