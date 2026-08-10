import FormalConjectures.Util.ProblemImports
open Nat Int

lemma exists_prime_div_factorial (n : ℕ) (hn : 6 ≤ n) : ∃ p, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n := by
  have h_pos : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) h_pos
  use p
  refine ⟨hp_prime, hp1, ?_⟩
  have h_le : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  exact hp2.trans h_le
