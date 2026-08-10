import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

lemma helper (n : ℕ) (hn : 1 < n) : (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn_real : 1 < (n : ℝ) := by positivity
  have h_one : (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by simp
  rw [h_one]
  have h_lt : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) := by
    have h_div_pos : 0 < 1 / (n : ℝ) := by positivity
    have h_base_lt : (1 : ℝ) ^ (1 / (n : ℝ)) < (n : ℝ) ^ (1 / (n : ℝ)) := by
      exact Real.rpow_lt_rpow zero_le_one hn_real h_div_pos
    rw [Real.one_rpow] at h_base_lt
    exact h_base_lt
  exact Real.rpow_lt_rpow_of_exponent_lt hn_real h_lt
