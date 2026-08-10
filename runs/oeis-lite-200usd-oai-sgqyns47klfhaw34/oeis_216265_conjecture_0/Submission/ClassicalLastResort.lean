import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

def P : Prop := ∀ n : ℕ, n > 13 → A216265 n > 0

-- all expected to fail if uncommented
-- example : P := Classical.choice (inferInstance : Nonempty P)
-- example : P := Classical.choice (Classical.choice (show (Nonempty P ∨ Nonempty (¬ P)) from ?_))
-- example : P := of_decide_eq_true (rfl : decide P = true)

example : Decidable P := inferInstance
example : Subsingleton P := inferInstance
#check (Classical.propComplete P)
#check (Classical.choice)
