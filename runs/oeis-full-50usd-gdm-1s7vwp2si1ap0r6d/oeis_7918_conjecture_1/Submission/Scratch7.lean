import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

theorem prime_case (n : ℕ) (h_n : 1 < n) (hp : Nat.Prime n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have h_a : a n = n := by
    dsimp [a]
    rw [Nat.find_eq_iff]
    refine ⟨⟨hp, le_refl _⟩, ?_⟩
    intro m hm ⟨_, h_le⟩
    omega
  rw [h_a]
  have h_n_real : 1 < (n : ℝ) := by
    exact_mod_cast h_n
  have h_inv_pos : 0 < 1 / (n : ℝ) := by
    exact div_pos zero_lt_one (by linarith)
  have h_rpow_gt_one : 1 < (n : ℝ) ^ (1 / (n : ℝ)) := by
    exact Real.one_lt_rpow h_n_real h_inv_pos
  -- Now we want to prove (n : ℝ) ^ 1 < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ)))
  have h_rpow : (n : ℝ) ^ (1 : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
    exact Real.rpow_lt_rpow_of_exponent_lt h_n_real h_rpow_gt_one
  rw [Real.rpow_one] at h_rpow
  exact h_rpow
