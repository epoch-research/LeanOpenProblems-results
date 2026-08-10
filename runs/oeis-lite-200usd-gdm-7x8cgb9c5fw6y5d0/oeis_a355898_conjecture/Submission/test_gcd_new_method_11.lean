import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def B0 : ℕ := 3
def B1 : ℕ := 4

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

lemma B_mod_5_vals (n : ℕ) : B n % 5 = 3 ∨ B n % 5 = 4 ∨ B n % 5 = 2 ∨ B n % 5 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · unfold B B0; decide
    · rcases n with _ | n
      · unfold B B1; decide
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec]
        have ih1 := ih (n + 1) (by omega)
        have ih2 := ih n (by omega)
        rw [Nat.add_mod]
        omega
