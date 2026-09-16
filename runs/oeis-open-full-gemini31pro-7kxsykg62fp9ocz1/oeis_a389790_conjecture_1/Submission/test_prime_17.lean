import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_eq_5 : next_prime 3 = 5 := by
  have h_in : 5 ∈ {k : ℕ | Nat.Prime k ∧ 3 < k} := by
    dsimp
    refine ⟨?_, by decide⟩
    exact by decide
  have h_le : next_prime 3 ≤ 5 := Nat.sInf_le h_in
  have h_prime : Nat.Prime (next_prime 3) := by
    have h_nonempty : {k : ℕ | Nat.Prime k ∧ 3 < k}.Nonempty := by
      rcases Nat.exists_infinite_primes (3 + 1) with ⟨p, hp1, hp2⟩
      exact ⟨p, hp2, hp1⟩
    exact (Nat.sInf_mem h_nonempty).1
  have h_gt : 3 < next_prime 3 := by
    have h_nonempty : {k : ℕ | Nat.Prime k ∧ 3 < k}.Nonempty := by
      rcases Nat.exists_infinite_primes (3 + 1) with ⟨p, hp1, hp2⟩
      exact ⟨p, hp2, hp1⟩
    exact (Nat.sInf_mem h_nonempty).2
  have h_not_4 : next_prime 3 ≠ 4 := by
    intro h
    rw [h] at h_prime
    revert h_prime
    decide
  omega
