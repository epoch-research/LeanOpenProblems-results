import FormalConjecturesUtil
import Submission.LogarithmicSmoothCommutator
import Submission.PrimeDiscrepancy

/-! Bounded total variation of the logarithmic commutator as the smoothness
cutoff changes. The jumps are weighted UNSIGNED winner counts, except at one
endpoint. A concrete outside-prime term is not bounded by its cutoff jump. -/

namespace Erdos371SmoothCutoffVariation

open Finset Filter Erdos371LogarithmicSmoothCommutator Erdos371PrimeDiscrepancy
open scoped Topology

noncomputable def pair (Y n : ℕ) : ℝ := smooth Y n*smooth Y (n+1)

lemma pair_eq_indicator (Y n : ℕ) : pair Y n = if 0<n ∧ winner n<Y then 1 else 0 := by
  unfold pair smooth winner
  by_cases hn : n=0
  · simp [hn]
  · have hn0 : 0<n := by omega
    simp only [hn0,Nat.zero_lt_succ,true_and,max_lt_iff]
    split_ifs <;> simp_all

lemma pair_jump (p n : ℕ) : pair (p+1) n-pair p n =
    if 0<n ∧ winner n=p then 1 else 0 := by
  simp only [pair_eq_indicator]
  split_ifs <;> norm_num <;> omega

noncomputable def jump (p N : ℕ) : ℝ :=
  weightedSum (smooth (p+1)) N-weightedSum (smooth p) N

noncomputable def interior (p N : ℕ) : ℝ :=
  ∑ n ∈ range N, if 0<n ∧ winner n=p then logStep n else 0

noncomputable def endpoint (p N : ℕ) : ℝ :=
  if 0<N ∧ winner N=p then Real.log (N:ℝ) else 0

lemma jump_eq (p N : ℕ) : jump p N = interior p N-endpoint p N := by
  rw [jump,weightedSum_eq_boundary _ (smooth_mul (p+1)),
    weightedSum_eq_boundary _ (smooth_mul p)]
  have he : (∑ n ∈ range N, smooth (p+1) n*smooth (p+1) (n+1)*logStep n)-
      (∑ n ∈ range N, smooth p n*smooth p (n+1)*logStep n) = interior p N := by
    rw [← sum_sub_distrib]
    unfold interior
    apply sum_congr rfl
    intro n hn
    rw [← sub_mul]
    change (pair (p+1) n-pair p n)*logStep n = _
    rw [pair_jump]
    split_ifs <;> ring
  have hb : Real.log (N:ℝ)*smooth (p+1) N*smooth (p+1) (N+1)-
      Real.log (N:ℝ)*smooth p N*smooth p (N+1) = endpoint p N := by
    simp only [mul_assoc,← mul_sub]
    change Real.log (N:ℝ)*(pair (p+1) N-pair p N) = _
    rw [pair_jump]
    unfold endpoint
    split_ifs <;> ring
  linarith

lemma interior_nonneg (p N : ℕ) : 0 ≤ interior p N := by
  unfold interior
  apply sum_nonneg
  intro n hn
  split_ifs
  · exact logStep_nonneg n
  · rfl

lemma endpoint_nonneg (p N : ℕ) : 0 ≤ endpoint p N := by
  unfold endpoint
  split_ifs
  · exact Real.log_natCast_nonneg N
  · rfl

lemma interior_sum_le (s : Finset ℕ) (N : ℕ) :
    (∑ p ∈ s, interior p N) ≤ Real.log (N:ℝ) := by
  unfold interior
  rw [sum_comm,← logStep_sum]
  apply sum_le_sum
  intro n hn
  simp only [ite_and,sum_ite_irrel,sum_ite_eq]
  split_ifs <;> (try simp only [sum_const_zero]) <;> first | exact le_rfl | exact logStep_nonneg n

lemma endpoint_sum_le (s : Finset ℕ) (N : ℕ) :
    (∑ p ∈ s, endpoint p N) ≤ Real.log (N:ℝ) := by
  simp only [endpoint,ite_and,sum_ite_irrel,sum_ite_eq]
  split_ifs <;> (try simp only [sum_const_zero]) <;> first | exact le_rfl | exact Real.log_natCast_nonneg N

lemma jump_nonneg_of_ne {p N : ℕ} (h : winner N ≠ p) : 0 ≤ jump p N := by
  rw [jump_eq]
  simpa [endpoint,h] using interior_nonneg p N

lemma jump_le_log (p N : ℕ) : jump p N ≤ Real.log (N:ℝ) := by
  have hi : interior p N ≤ Real.log (N:ℝ) := by simpa using interior_sum_le {p} N
  rw [jump_eq]
  linarith [endpoint_nonneg p N]

/-- Summing absolute cutoff jumps costs only `2 log N`, uniformly in the
finite collection of cutoffs. This is not the sum of absolute prime groups. -/
theorem total_variation_bound (s : Finset ℕ) (N : ℕ) :
    (∑ p ∈ s, |jump p N|) ≤ 2*Real.log (N:ℝ) := by
  have hpoint (p : ℕ) : |jump p N| ≤ interior p N+endpoint p N := by
    rw [jump_eq]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (interior_nonneg p N),
      abs_of_nonneg (endpoint_nonneg p N)])
  calc
    _ ≤ ∑ p ∈ s, (interior p N+endpoint p N) := sum_le_sum (fun p hp => hpoint p)
    _ = (∑ p ∈ s, interior p N)+(∑ p ∈ s, endpoint p N) := sum_add_distrib
    _ ≤ _ := by linarith [interior_sum_le s N,endpoint_sum_le s N]

theorem variation_mean_zero (s : ℕ → Finset ℕ) :
    Tendsto (fun N : ℕ => (∑ p ∈ s N, |jump p N|)/N) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => 2*(Real.log (N:ℝ)/N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    positivity
  · intro N
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (total_variation_bound (s N) N) (Nat.cast_nonneg N)

def smoothInt (Y n : ℕ) : ℤ := if 0<n ∧ P n<Y then 1 else 0

def outsideInt (p N : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 (N/p), smoothInt p a*(smoothInt p (a*p-1)-smoothInt p (a*p+1))

lemma smoothInt_cast (Y n : ℕ) : (smoothInt Y n:ℝ)=smooth Y n := by
  unfold smoothInt smooth
  split_ifs <;> norm_num

lemma outsideInt_cast (p N : ℕ) : (outsideInt p N:ℝ)=bilinear (smooth p) p N := by
  simp only [outsideInt,bilinear,Int.cast_sum,Int.cast_mul,Int.cast_sub,smoothInt_cast]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
lemma outside_seventeen : outsideInt 17 31213 = -4 := by
  decide +kernel

lemma outside_seventeen_real : bilinear (smooth 17) 17 31213 = -4 := by
  rw [← outsideInt_cast,outside_seventeen]
  norm_num

/-- The primary outside-prime contribution can exceed the ENTIRE cutoff jump
in absolute value. The omitted changes must provide cancellation in this
example; they cannot be discarded from the jump identity. -/
theorem primary_term_not_bounded_by_jump :
    |jump 17 31213| < |Real.log 17*bilinear (smooth 17) 17 31213| := by
  have hn : winner 31213 ≠ 17 := by decide +kernel
  rw [abs_of_nonneg (jump_nonneg_of_ne hn),outside_seventeen_real]
  have hl : 0 < Real.log 17 := Real.log_pos (by norm_num)
  have he : |Real.log 17*(-4)| = 4*Real.log 17 := by
    rw [abs_mul,abs_of_pos hl]
    norm_num
    ring
  rw [he]
  apply (jump_le_log 17 31213).trans_lt
  have hh := Real.log_lt_log (by norm_num : (0:ℝ)<31213)
    (by norm_num : (31213:ℝ)<17^4)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

end Erdos371SmoothCutoffVariation

#print axioms Erdos371SmoothCutoffVariation.total_variation_bound
#print axioms Erdos371SmoothCutoffVariation.variation_mean_zero
#print axioms Erdos371SmoothCutoffVariation.primary_term_not_bounded_by_jump
