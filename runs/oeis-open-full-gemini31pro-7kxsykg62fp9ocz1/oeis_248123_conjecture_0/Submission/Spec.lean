import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A248123 (n : ℕ) : ℕ :=
  let catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)
  sInf {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n)}

theorem oeis_248123_conjecture_0 (n : ℕ) (hn : n > 0) : A248123 n > 0 := by
  sorry

theorem oeis_248123_conjecture_0.disproof : ¬ (∀ (n : ℕ), n > 0 → A248123 n > 0) := by
  sorry
