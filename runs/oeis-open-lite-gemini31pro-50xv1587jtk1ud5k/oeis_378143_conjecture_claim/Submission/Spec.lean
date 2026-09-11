import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A378143 (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n h
  rcases n with _ | _ | n
  · exact Or.inl (by norm_num)
  · exact Or.inl (by norm_num)
  · sorry

theorem oeis_378143_conjecture_claim.disproof : ¬ (type_of% @oeis_378143_conjecture_claim) := by
  sorry
