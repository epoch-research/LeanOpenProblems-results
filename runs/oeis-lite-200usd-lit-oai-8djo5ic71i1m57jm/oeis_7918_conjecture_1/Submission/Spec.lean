import FormalConjectures.Util.ProblemImports

open Nat

/--
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

/--
Conjecture: if n > 1, then a(n) < n^(n^(1/n)). - _Thomas Ordowski_, Feb 23 2023
-/
theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  sorry
