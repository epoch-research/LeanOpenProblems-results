import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

-- We mock A355898_loop here to make it compile, but we'll use the real one in Spec.lean.
def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b => (b, a)

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

lemma B_mod_5_vals (n : ℕ) : B n % 5 = 3 ∨ B n % 5 = 4 ∨ B n % 5 = 2 ∨ B n % 5 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · unfold B B0 S3772_fst; decide
    · rcases n with _ | n
      · unfold B B1 S3772_snd; decide
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec]
        have ih1 := ih (n + 1) (by omega)
        have ih2 := ih n (by omega)
        omega
