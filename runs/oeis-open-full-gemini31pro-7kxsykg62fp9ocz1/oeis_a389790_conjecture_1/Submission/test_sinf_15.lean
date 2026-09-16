import FormalConjectures.Util.ProblemImports
open Classical

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_gt (r : ℕ) : r < next_prime r := by
  have h : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    rcases Nat.exists_infinite_primes r with ⟨p, hr, hp⟩
    exact ⟨p, hp, hr⟩
  exact Nat.sInf_mem h |>.2
