import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma a_eval : next_prime 10 = 11 := by
  have h_in : 11 ∈ {k : ℕ | Nat.Prime k ∧ 10 < k} := ⟨by decide, by decide⟩
  have h_le : next_prime 10 ≤ 11 := Nat.sInf_le h_in
  have h_prime : Nat.Prime (next_prime 10) := by
    have h_nonempty : {k : ℕ | Nat.Prime k ∧ 10 < k}.Nonempty := by
      rcases Nat.exists_infinite_primes (10 + 1) with ⟨p, hp1, hp2⟩
      exact ⟨p, hp2, hp1⟩
    exact (Nat.sInf_mem h_nonempty).1
  have h_gt : 10 < next_prime 10 := by
    have h_nonempty : {k : ℕ | Nat.Prime k ∧ 10 < k}.Nonempty := by
      rcases Nat.exists_infinite_primes (10 + 1) with ⟨p, hp1, hp2⟩
      exact ⟨p, hp2, hp1⟩
    exact (Nat.sInf_mem h_nonempty).2
  revert h_prime
  revert h_gt
  revert h_le
  -- the rest can be done with omega and decide
  intro h1 h2 h3
  omega
