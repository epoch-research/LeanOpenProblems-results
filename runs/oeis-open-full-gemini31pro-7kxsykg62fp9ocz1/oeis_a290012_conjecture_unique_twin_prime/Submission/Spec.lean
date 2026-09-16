import FormalConjectures.Util.ProblemImports

open Nat Set Finset

noncomputable def A290012 (n : ℕ) : ℕ :=
  let S_n : ℕ := (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)
  sInf { p : ℕ | p.Prime ∧ S_n ≤ p ^ 2 }

theorem oeis_a290012_conjecture_unique_twin_prime :
  ∀ n : ℕ, 1 ≤ n → (A290012 (n + 1) = A290012 n + 2 ↔ n = 2) := sorry

theorem oeis_a290012_conjecture_unique_twin_prime.disproof : ¬ (type_of% @oeis_a290012_conjecture_unique_twin_prime) := by
  intro h
  sorry
