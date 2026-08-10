import FormalConjectures.Util.ProblemImports
open Nat

abbrev GoalAt (n : ℕ) : Prop := ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
abbrev TargetT : Prop := ∀ n : ℕ, n > 0 → GoalAt n

-- Check what instances are available for function/proposition types.
#synth Subsingleton (GoalAt 1)
#synth Subsingleton TargetT
#synth Inhabited (True → GoalAt 1)
#synth Inhabited (False → GoalAt 1)
#synth Nonempty (False → GoalAt 1)
#synth Inhabited (∀ h : False, GoalAt 1)
#synth Inhabited (∀ n : Fin 0, GoalAt n)

example : TargetT := by
  -- Attempt local recursive/default instance for each goal.
  letI instGoal (n : ℕ) : Inhabited (GoalAt n) := ⟨default⟩
  exact fun n hn => default

#print axioms _example
