import Submission.TenThousandPoolMultiplicity
import Submission.DensityCutoffRefinement

/-!
# A strict gain beyond the certified ten-thousand-band exponent

The fixed positive count supplied by the ten-thousand-band argument can be
refined once. The resulting margin is positive but is not asserted to
be uniform under repeated refinement. This does not settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

set_option maxHeartbeats 3000000

/-- A positive rational margin beyond the previous rational threshold.
The natural parameter K is provided by the existing density-sensitive
cutoff refinement, not by an unproved prime-supply hypothesis. -/
theorem exists_ten_thousand_pool_strict_gain :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ γ : ℝ,
      γ < 2441371/4000002 + 1/(40000020*(K : ℝ)) →
      {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,hC,HC⟩ := exists_ten_thousand_pool_smooth_prime_count
  obtain ⟨K,C',hK,_hC',_hratio,Hsmall⟩ :=
    exists_smaller_cutoff_single_log_count 40000020 15586310 C
      (by decide) (by decide) (by decide) hC HC
  refine ⟨K,hK,?_⟩
  intro γ hγ
  apply infinite_g_gt_of_single_log_smooth_count (40000020*K) (15586310*K-1)
    C' (by omega) Hsmall γ
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsub : ((15586310*K-1 : ℕ) : ℝ) = 15586310*(K : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 15586310*K)]
    push_cast
    rfl
  have he : 1-((15586310*K-1 : ℕ) : ℝ)/((40000020*K : ℕ) : ℝ) =
      2441371/4000002+1/(40000020*(K : ℝ)) := by
    rw [hsub]
    push_cast
    field_simp
    ring
  rwa [he]

/-- In particular the exact rational endpoint, previously excluded by a
strict comparison in the band-only transfer, is attained. -/
theorem infinite_g_gt_ten_thousand_pool_endpoint :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(2441371/4000002 : ℝ)}.Infinite := by
  obtain ⟨K,hK,H⟩ := exists_ten_thousand_pool_strict_gain
  apply H
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpos : (0 : ℝ) < 1/(40000020*(K : ℝ)) := by positivity
  linarith

/-- The new exponent exceeds the rational threshold strictly, although
no numerical lower bound for that excess is claimed here. -/
theorem exists_exponent_above_ten_thousand_pool :
    ∃ γ : ℝ, 2441371/4000002 < γ ∧
      {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨K,hK,H⟩ := exists_ten_thousand_pool_strict_gain
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpos : (0 : ℝ) < 1/(40000020*(K : ℝ)) := by positivity
  refine ⟨2441371/4000002 + (1/(40000020*(K : ℝ)))/2, by linarith, H _ ?_⟩
  linarith

/-- The original conclusion holds at the former excluded epsilon endpoint
as well as throughout the previously established open range. -/
theorem erdos_821_ten_thousand_pool_closed_range (ε : ℝ) (hε : 1558631/4000002 ≤ ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  obtain ⟨K,hK,H⟩ := exists_ten_thousand_pool_strict_gain
  apply H
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpos : (0 : ℝ) < 1/(40000020*(K : ℝ)) := by positivity
  linarith

end Erdos821
