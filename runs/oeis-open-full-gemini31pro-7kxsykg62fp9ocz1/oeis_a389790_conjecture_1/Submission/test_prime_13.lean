import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_min (r : ℕ) {k : ℕ} (hk_prime : Nat.Prime k) (hk_gt : r < k) : next_prime r ≤ k := by
  have h_in : k ∈ {k' : ℕ | Nat.Prime k' ∧ r < k'} := ⟨hk_prime, hk_gt⟩
  exact Nat.sInf_le h_in
