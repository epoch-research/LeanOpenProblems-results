import Submission.RoughPartGoodPairs

/-! Rough parts exceed every fixed power N^(1-1/(q+1)) on density one
when B is subpower. This strengthens the earlier fixed 3/4 exponent. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def smallRoughPartPowerCount (B q N : ℕ) : ℕ :=
  ((range N).filter fun n => (roughPrimePart B (n+1))^(q+1) ≤ N^q).card

theorem smallRoughPartPowerCount_log_bound (B q N : ℕ) (_hN : 1 < N) :
    (smallRoughPartPowerCount B q N : ℝ) * Real.log N ≤
      (q+1 : ℝ) * N + 4*(q+1 : ℝ) * N * Real.log (B + 1 : ℝ) := by
  let S := (Finset.range N).filter fun n => (roughPrimePart B (n + 1))^(q+1) ≤ N^q
  have hterm (n : ℕ) (hn : n ∈ S) : Real.log N ≤
      (q+1 : ℝ) * (Real.log N - Real.log (roughPrimePart B (n + 1))) := by
    have hpow := (Finset.mem_filter.mp hn).2
    have hp : (roughPrimePart B (n + 1) : ℝ)^(q+1) ≤ (N : ℝ)^q := by exact_mod_cast hpow
    have ha0 : (0 : ℝ) < roughPrimePart B (n + 1) := by exact_mod_cast roughPrimePart_pos B (n + 1)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (roughPrimePart B (n + 1) : ℝ)^(q+1)) hp
    simp only [Real.log_pow] at hlog
    push_cast at hlog
    nlinarith
  calc
    _ = ∑ n ∈ S, Real.log N := by simp [S, smallRoughPartPowerCount]
    _ ≤ ∑ n ∈ S, (q+1 : ℝ) * (Real.log N - Real.log (roughPrimePart B (n + 1))) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range N, (q+1 : ℝ) * (Real.log N - Real.log (roughPrimePart B (n + 1))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n hn _ => mul_nonneg (by positivity) (roughPrimePart_log_deficit_nonneg B N n hn))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      have h := roughPrimePart_log_deficit_sum_bound B N
      nlinarith


lemma smallRoughPartPowerCount_ratio_bound (B q N : ℕ) (hN : 1 < N) :
    (smallRoughPartPowerCount B q N : ℝ) / N ≤
      (q+1 : ℝ) / Real.log N + 4*(q+1 : ℝ) * (Real.log (B + 1 : ℝ) / Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := smallRoughPartPowerCount_log_bound B q N hN
  have he : (q+1 : ℝ) / Real.log N + 4*(q+1 : ℝ) * (Real.log (B + 1 : ℝ) / Real.log N) =
      ((q+1 : ℝ) * N + 4*(q+1 : ℝ) * N * Real.log (B + 1 : ℝ)) / (N * Real.log N) := by field_simp
  rw [he, le_div_iff₀ (mul_pos hN0 hlog)]
  convert h using 1; field_simp


theorem smallRoughPartPowerCount_succ_tendsto_zero (B : ℕ → ℕ) (q : ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => (smallRoughPartPowerCount (B N) q (N + 1) : ℝ) / N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have ht := ((tendsto_inv_atTop_zero.comp hlog).const_mul (q+1 : ℝ)).add
    ((subpower_log_ratio_succ B hB).const_mul (4*(q+1) : ℝ))
  simp only [mul_zero, add_zero] at ht
  have hs : Tendsto (fun N => (smallRoughPartPowerCount (B N) q (N + 1) : ℝ) / (N + 1 : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
      smallRoughPartPowerCount_ratio_bound (B N) q (N + 1) (by omega)
  have hr : Tendsto (fun N : ℕ => (N + 1 : ℝ) / N) atTop (nhds 1) := by
    have ht := tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    field_simp
  have hp := hs.mul hr
  simp only [zero_mul] at hp
  apply hp.congr
  intro N
  field_simp

#print axioms smallRoughPartPowerCount_succ_tendsto_zero
end Erdos371
