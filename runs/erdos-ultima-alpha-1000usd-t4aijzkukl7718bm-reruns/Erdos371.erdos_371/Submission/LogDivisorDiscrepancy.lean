import FormalConjecturesUtil
import Submission.WeightedLargeDivisorEnergy

/-! The unrestricted signed discrepancy is approximated in mean by a
logarithmically weighted sum of all divisor-restricted groups. The cutoff
restriction in the linear energy estimate cannot be omitted in this identity. -/

namespace Erdos371LogDivisorDiscrepancy

open Finset Filter Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371LargeDivisorSignedEnergy Erdos371RadicalLogMean
open Erdos371WeightedLargeDivisorEnergy (weight)
open scoped Topology

noncomputable def fullSum (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
    weight N q * restrictedGroup p q N

lemma member_signed_weight_expand (N p q : ℕ) :
    weight N q * restrictedGroup p q N =
      ∑ n ∈ range N,
        (sign n : ℝ) * (if winner n=p ∧ q ∣ lower n then weight N q else 0) := by
  unfold restrictedGroup members
  rw [mul_sum, sum_filter]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

lemma fullSum_eq (N : ℕ) :
    fullSum N = ∑ n ∈ range N, (sign n : ℝ) * level N (lower n) := by
  unfold fullSum
  simp_rw [member_signed_weight_expand]
  conv_lhs => arg 2; ext p; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  simp_rw [← mul_sum]
  rw [Erdos371WeightedLargeDivisorEnergy.input_weight_sum (mem_range.mp hn)]
  by_cases hn0 : n=0
  · subst n
    have he : lower 0=0 := by decide +kernel
    simp [he,level]
  · rw [if_neg hn0]

lemma input_error_le {N : ℕ} (hN : 1 < N) {n : ℕ} (hn : n < N) :
    |(sign n : ℝ)-(sign n : ℝ)*level N (lower n)| ≤
      (1-level N n)+(1-level N (n+1)) := by
  have h₀ := level_bounds hN (show n ≤ N by omega)
  have h₁ := level_bounds hN (show n+1 ≤ N by omega)
  unfold sign lower
  split_ifs <;> simp only [Int.cast_one,Int.cast_neg,one_mul,neg_mul] <;>
    apply abs_le.mpr <;> constructor <;> linarith

lemma error_bound {N : ℕ} (hN : 1 < N) :
    |(total N : ℝ)-fullSum N| ≤ 2*defect N := by
  have hn (n : ℕ) (hn : n ≤ N) : 0 ≤ 1-level N n :=
    sub_nonneg.mpr (level_bounds hN hn).2
  have hleft : (∑ n ∈ range N, (1-level N n)) ≤ defect N := by
    unfold defect
    rw [sum_range_succ]
    exact le_add_of_nonneg_right (hn N le_rfl)
  have hright : (∑ n ∈ range N, (1-level N (n+1))) ≤ defect N := by
    unfold defect
    rw [sum_range_succ']
    exact le_add_of_nonneg_right (hn 0 (Nat.zero_le N))
  rw [fullSum_eq,total,Int.cast_sum,← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range N, |(sign n : ℝ)-(sign n : ℝ)*level N (lower n)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, ((1-level N n)+(1-level N (n+1))) :=
      sum_le_sum fun n hn => input_error_le hN (mem_range.mp hn)
    _ ≤ _ := by rw [sum_add_distrib]; linarith

lemma mean_error_tendsto_zero :
    Tendsto (fun N : ℕ => ((total N : ℝ)-fullSum N)/N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hu : Tendsto (fun N : ℕ => 2*(defect N/N)) atTop (𝓝 0) := by
    simpa using defect_mean_tendsto_zero.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 1] with N hN
    change |((total N : ℝ)-fullSum N)/N| ≤ 2*(defect N/N)
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (error_bound hN) (Nat.cast_nonneg (α := ℝ) N)

/-- This is an equivalence, not a proof that either side holds. -/
theorem density_half_iff_fullSum_mean_zero :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ => fullSum N/N) atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  constructor
  · intro h
    have hh := h.sub mean_error_tendsto_zero
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    dsimp
    ring
  · intro h
    have hh := h.add mean_error_tendsto_zero
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    dsimp
    ring

end Erdos371LogDivisorDiscrepancy

#print axioms Erdos371LogDivisorDiscrepancy.error_bound
#print axioms Erdos371LogDivisorDiscrepancy.density_half_iff_fullSum_mean_zero
