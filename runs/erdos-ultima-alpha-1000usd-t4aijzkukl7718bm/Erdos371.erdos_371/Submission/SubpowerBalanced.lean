import Submission.BalancedBilinear
import Submission.SubpowerTail

/-! Combining the subpower roughness cutoff with the two-coordinate
truncation. The central rectangular cancellation remains unproved. -/

namespace Erdos371

open Filter in
theorem exists_balanced_cutoff_of_subpower (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N,
          roughMixedDivisorTail (B N) (nearLinearCutoff N) (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum (B N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
        atTop (nhds 0) ∧
      ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
        Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N,
            balancedBilinearSum (B N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
          atTop (nhds 0)) := by
  obtain ⟨K, hK, hKB, hKe⟩ := exists_slow_square_cutoff B
    (fun N => (roughNumberCount (B N) (N + 2) : ℝ) / N)
    hBatTop (growing_roughNumberCount_succsucc_tendsto B hBatTop) (fun N => by positivity)
  have herr : Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N,
          roughMixedDivisorTail (B N) (nearLinearCutoff N) (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum (B N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
        atTop (nhds 0) := by
    have ht := hKe.const_mul (3 : ℝ)
    simp only [mul_zero] at ht
    apply squeeze_zero_norm' _ ht
    filter_upwards [hKB] with N hKN
    rw [norm_div, Real.norm_natCast]
    calc
      _ ≤ (3 * (K N + 1 : ℝ)^2 * roughNumberCount (B N) (N + 2)) / N :=
        div_le_div_of_nonneg_right (balancedBilinearSum_error_bound _ _ _ _
          (nearLinearCutoff_le_self N) hKN) (Nat.cast_nonneg N)
      _ = _ := by ring
  refine ⟨K, hK, herr, ?_⟩
  rw [density_iff_subpower_rough_mixed_tail B hB]
  constructor
  · intro h
    have ht := h.sub herr
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    have ht := h.add herr
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring

open Filter in
/-- A stronger equivalent remainder, not a proof that this remainder has
zero mean. Its least-prime-factor cutoff is of size exp(sqrt(log N)). -/
theorem exists_subpower_balanced_cutoff :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧
      ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
        Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N,
            balancedBilinearSum (subpowerCutoff N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
          atTop (nhds 0)) := by
  obtain ⟨K, hK, _, he⟩ := exists_balanced_cutoff_of_subpower subpowerCutoff
    subpowerCutoff_atTop subpowerCutoff_log_ratio_tendsto_zero
  exact ⟨K, hK, he⟩

#print axioms exists_balanced_cutoff_of_subpower
#print axioms exists_subpower_balanced_cutoff
end Erdos371
