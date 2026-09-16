import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_eq_find (r : ℕ) : 
  next_prime r = Nat.find (by
    have h : ∃ p, Nat.Prime p ∧ r < p := by
      rcases Nat.exists_infinite_primes (r + 1) with ⟨p, hp1, hp2⟩
      exact ⟨p, hp2, hp1⟩
    exact h
  ) := by
  have h_nonempty : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    rcases Nat.exists_infinite_primes (r + 1) with ⟨p, hp1, hp2⟩
    exact ⟨p, hp2, hp1⟩
  rw [next_prime]
  exact Nat.sInf_def h_nonempty
