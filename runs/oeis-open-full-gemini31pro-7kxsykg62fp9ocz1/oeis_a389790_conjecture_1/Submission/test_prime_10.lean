import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_prop (r : ℕ) : Nat.Prime (next_prime r) ∧ r < next_prime r := by
  have h_nonempty : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    rcases Nat.exists_infinite_primes (r + 1) with ⟨p, hp1, hp2⟩
    exact ⟨p, hp2, hp1⟩
  have h := Nat.sInf_def h_nonempty
  have h2 := Nat.find_spec h_nonempty
  unfold next_prime
  rw [h]
  exact h2
