import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def B0 : ℕ := 3
def B1 : ℕ := 4

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

lemma B_mod_5_pairs (n : ℕ) :
  (B n % 5 = 3 ∧ B (n + 1) % 5 = 4) ∨
  (B n % 5 = 4 ∧ B (n + 1) % 5 = 2) ∨
  (B n % 5 = 2 ∧ B (n + 1) % 5 = 1) ∨
  (B n % 5 = 1 ∧ B (n + 1) % 5 = 3) := by
  induction n with
  | zero =>
    unfold B B0 B1
    decide
  | succ n ih =>
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left
      constructor
      · exact h2
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec, Nat.add_mod, h1, h2]
        decide
    · right; right; left
      constructor
      · exact h2
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec, Nat.add_mod, h1, h2]
        decide
    · right; right; right
      constructor
      · exact h2
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec, Nat.add_mod, h1, h2]
        decide
    · left
      constructor
      · exact h2
      · have h_rec : B (n + 2) = B (n + 1) + B n := rfl
        rw [h_rec, Nat.add_mod, h1, h2]
        decide
