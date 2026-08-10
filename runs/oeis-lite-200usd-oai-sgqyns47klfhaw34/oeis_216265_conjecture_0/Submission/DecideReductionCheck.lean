import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
def P : Prop := ∀ n : ℕ, n > 13 → A216265 n > 0

noncomputable example : Decidable P := by classical exact inferInstance

-- These should fail:
-- noncomputable example : P := by classical exact of_decide_eq_true (rfl : decide P = true)
-- noncomputable example : ¬ P := by classical exact of_decide_eq_false (rfl : decide P = false)

#check of_decide_eq_false
#check decide_eq_false_iff_not
#check decidable_of_iff
#reduce (decide (A216265 14 > 0))
#eval A216265 14
#eval A216265 13
