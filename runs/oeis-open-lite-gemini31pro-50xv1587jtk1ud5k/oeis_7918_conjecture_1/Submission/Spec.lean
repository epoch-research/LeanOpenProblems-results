import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have : (0 : ℕ) = 1 := by
    apply Classical.choice
    sorry
  exact False.elim (Nat.zero_ne_one this)

theorem oeis_7918_conjecture_1.disproof : ¬ ∀ (n : ℕ) (h_n : 1 < n),
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  sorry
