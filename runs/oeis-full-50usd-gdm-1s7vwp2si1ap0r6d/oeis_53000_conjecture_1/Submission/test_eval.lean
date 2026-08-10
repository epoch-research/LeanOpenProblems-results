import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/--
Conjecture: a(n) <= 1+phi(n).
-/
@[category research open]
theorem oeis_53000_conjecture_1_test (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  have h_exists : ∃ p, Nat.Prime p ∧ p > n ^ 2 := by
    rcases Nat.exists_infinite_primes (n ^ 2 + 1) with ⟨p, hp_ge, hp_prime⟩
    refine ⟨p, hp_prime, ?_⟩
    omega
  have hS : {p | Nat.Prime p ∧ p > n ^ 2}.Nonempty := by
    rcases h_exists with ⟨p, hp_prime, hp_gt⟩
    exact ⟨p, hp_prime, hp_gt⟩
  have h_mem : sInf {p | Nat.Prime p ∧ p > n ^ 2} ∈ {p | Nat.Prime p ∧ p > n ^ 2} := Nat.sInf_mem hS
  have h_gt : sInf {p | Nat.Prime p ∧ p > n ^ 2} > n ^ 2 := h_mem.2
  have h_bertrand : sInf {p | Nat.Prime p ∧ p > n ^ 2} ≤ 2 * n ^ 2 := by
    have h_pos : n ^ 2 ≠ 0 := by
      have hn2_pos : n ^ 2 > 0 := by positivity
      omega
    rcases exists_prime_lt_and_le_two_mul (n ^ 2) h_pos with ⟨p, hp_prime, hp_gt, hp_le⟩
    have hp_mem : p ∈ {p | Nat.Prime p ∧ p > n ^ 2} := ⟨hp_prime, hp_gt⟩
    have h_le := Nat.sInf_le hp_mem
    exact le_trans h_le hp_le
  sorry

#print axioms oeis_53000_conjecture_1_test
