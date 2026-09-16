import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_eq_3 : next_prime 2 = 3 := by
  have h1 : Nat.Prime (next_prime 2) ∧ 2 < next_prime 2 := by
    have h_nonempty : {k : ℕ | Nat.Prime k ∧ 2 < k}.Nonempty := by
      rcases Nat.exists_infinite_primes (2 + 1) with ⟨p, hp1, hp2⟩
      exact ⟨p, hp2, hp1⟩
    exact Nat.sInf_mem h_nonempty
  have h2 : next_prime 2 ≤ 3 := by
    have h_in : 3 ∈ {k : ℕ | Nat.Prime k ∧ 2 < k} := ⟨Nat.prime_three, by decide⟩
    exact Nat.sInf_le h_in
  omega
