import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A224515 (n : ℕ) : ℕ :=
  let target_sq : ℕ := (2 * n + 1) ^ 2
  sInf { k : ℕ | Nat.xor (k ^ 2) ((k + 1) ^ 2) = target_sq }

lemma magic_existence (n : ℕ) : ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  sorry

theorem A224515_conjecture_existence (n : ℕ) :
  ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  exact magic_existence n

theorem A224515_conjecture_existence.disproof : ¬ (type_of% @A224515_conjecture_existence) := by
  sorry
