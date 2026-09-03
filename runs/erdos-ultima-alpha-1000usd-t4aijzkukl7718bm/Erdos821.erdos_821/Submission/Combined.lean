import Submission.Work
import Submission.Sieve

/-!
# An unconditional partial result for Erdős problem 821

The finite sieve and the smooth-prime pigeonhole construction prove a fixed
positive-power lower bound for the totient multiplicity. This is strictly weaker
than the original conjecture, which requires every exponent below one.
-/

namespace Erdos821

/-- Infinitely many totients have multiplicity exceeding a fixed positive
power of their value. The exponent furnished by this elementary argument is
not close to one. -/
theorem exists_positive_power_multiplicity :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  obtain ⟨t, ht, H⟩ := Sieve.exists_fixed_smooth_shifted_prime_density
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  refine ⟨2 / (t : ℝ), div_pos (by norm_num) (by linarith), ?_,
    infinite_g_gt_fixed_power_of_weak_density t ht H⟩
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- The original infinitude assertion holds uniformly above one fixed cutoff
strictly between zero and one. The remaining interval below the cutoff is not
settled by the elementary sieve argument. -/
theorem exists_epsilon_cutoff :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, ε₀ ≤ ε →
      {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  obtain ⟨δ, hδ, hδ1, hinf⟩ := exists_positive_power_multiplicity
  refine ⟨1 - δ, by linarith, by linarith, ?_⟩
  intro ε hε
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  obtain ⟨hnδ, hn0⟩ := hn
  have hnne : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnne
  exact (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 1 - ε ≤ δ)).trans_lt hnδ

#print axioms exists_epsilon_cutoff

#print axioms exists_positive_power_multiplicity

end Erdos821
