import FormalConjecturesUtil
import Submission.DilationCounterexample
import Submission.CofactorDensity
import Submission.SmoothDensity
import Submission.PeriodicDensity

/-! Doubling invariance and fixed-ratio separation together do not imply
balanced ascents for general heights. This is not an arithmetic disproof. -/

namespace Erdos371AmplifiedDilationObstruction

open Finset Filter DilationCounterexample
open scoped Topology

noncomputable def weight (n : ℕ) : ℝ := (1/2)^height n
noncomputable def weightSum (N : ℕ) : ℝ := ∑ n ∈ range N, weight n

lemma sum_range_two (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (2*N), f n) = ∑ n ∈ range N, (f (2*n)+f (2*n+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega, sum_range_succ, sum_range_succ,
      sum_range_succ, ih]
    ring

lemma weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

lemma weight_pair_le (n : ℕ) : weight (2*n)+weight (2*n+1) ≤ (3/2)*weight n := by
  simp only [weight,height_even,height_odd]
  split_ifs <;> rw [pow_add] <;> nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) (height n)]

lemma weightSum_two_le (N : ℕ) : weightSum (2*N) ≤ (3/2)*weightSum N := by
  rw [weightSum,sum_range_two,weightSum,mul_sum]
  exact sum_le_sum fun n _ => weight_pair_le n

lemma weightSum_dyadic_le (k : ℕ) : weightSum (2^k) ≤ (3/2)^k := by
  induction k with
  | zero => simp [weightSum,weight]
  | succ k ih =>
    rw [pow_succ',pow_succ']
    exact (weightSum_two_le _).trans (mul_le_mul_of_nonneg_left ih (by norm_num))

lemma weightSum_mono : Monotone weightSum := by
  intro M N hMN
  exact sum_le_sum_of_subset_of_nonneg (range_mono hMN) (fun n _ _ => weight_nonneg n)

lemma weight_mean_bound {N : ℕ} (hN : 0<N) :
    weightSum N / N ≤ (3/2)*(3/4)^(Nat.log 2 N) := by
  let k := Nat.log 2 N
  have hlo : (2:ℕ)^k ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hhi : N ≤ (2:ℕ)^(k+1) := (Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) N).le
  have hrlo : (2:ℝ)^k ≤ N := by exact_mod_cast hlo
  calc
    weightSum N / N ≤ (3/2:ℝ)^(k+1) / N :=
      div_le_div_of_nonneg_right ((weightSum_mono hhi).trans (weightSum_dyadic_le _))
        (Nat.cast_nonneg N)
    _ ≤ (3/2:ℝ)^(k+1) / 2^k :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hrlo
    _ = (3/2)*(3/4)^k := by
      rw [pow_succ,mul_div_right_comm,← div_pow]
      norm_num
      ring

lemma log_two_tendsto : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2^k)] with N hN
  exact Nat.le_log_of_pow_le (by norm_num) hN

lemma weight_mean_tendsto_zero :
    Tendsto (fun N : ℕ => weightSum N/N) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => (3/2:ℝ)*(3/4)^(Nat.log 2 N)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤3/4)
        (by norm_num : (3/4:ℝ)<1)).comp log_two_tendsto))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N =>
      div_nonneg (sum_nonneg fun n _ => weight_nonneg n) (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact weight_mean_bound hN

lemma low_height_count_bound (K N : ℕ) :
    (((range N).filter fun n => height n≤K).card:ℝ) ≤ 2^K*weightSum N := by
  rw [← sum_boole,weightSum,mul_sum]
  apply sum_le_sum
  intro n _
  by_cases hn : height n≤K
  · simp only [if_pos hn]
    have hh : (1/2:ℝ)^K ≤ weight n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have he : (2:ℝ)^K*(1/2)^K=1 := by rw [← mul_pow]; norm_num
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) K]
  · simp only [if_neg hn]
    exact mul_nonneg (by positivity) (weight_nonneg n)

lemma low_height_hasDensity_zero (K : ℕ) : {n | height n≤K}.HasDensity 0 := by
  have hu : Tendsto (fun N : ℕ => (2:ℝ)^K*(weightSum N/N)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul weight_mean_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    change {n | height n≤K}.partialDensity Set.univ N ≤ (2:ℝ)^K*(weightSum N/N)
    rw [Erdos371Exploration.partialDensity_eq_count,← mul_div_assoc]
    exact div_le_div_of_nonneg_right (low_height_count_bound K N) (Nat.cast_nonneg N)

/-- A strictly increasing amplification of the original model. -/
def amplified (n : ℕ) : ℕ := 2^(height n)^2

lemma amplify_strictMono : StrictMono (fun h : ℕ => 2^h^2) := by
  intro a b hab
  apply (Nat.pow_lt_pow_iff_right (by norm_num : 1<(2:ℕ))).mpr
  nlinarith

lemma amplified_lt_iff (m n : ℕ) : amplified m<amplified n ↔ height m<height n :=
  amplify_strictMono.lt_iff_lt

lemma amplified_even (n : ℕ) : amplified (2*n)=amplified n := by
  simp [amplified]

lemma amplified_adjacent_ne {n : ℕ} (hn : 2≤n) : amplified (n+1)≠amplified n := by
  intro h
  exact adjacent_ne hn (amplify_strictMono.injective h)

lemma amplified_not_density_half :
    ¬{n | amplified n<amplified (n+1)}.HasDensity (1/2) := by
  simpa only [amplified_lt_iff] using not_density_half


lemma amplification_ratio {a b C : ℕ} (hCa : C≤a) (hab : a<b) :
    C*2^a^2<2^b^2 := by
  have hC : C<2^a := hCa.trans_lt Nat.lt_two_pow_self
  calc
    C*2^a^2 < 2^a*2^a^2 := Nat.mul_lt_mul_of_pos_right hC (by positivity)
    _ = 2^(a+a^2) := (pow_add 2 a (a^2)).symm
    _ ≤ 2^b^2 := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- Neighbors in the amplified model escape every fixed multiplicative ratio. -/
theorem amplified_fixed_ratio_hasDensity_zero (C : ℕ) :
    {n | max (amplified n) (amplified (n+1)) ≤
      C*min (amplified n) (amplified (n+1))}.HasDensity 0 := by
  let S : Set ℕ := {n | height n≤C+2}
  have hS : S.HasDensity 0 := low_height_hasDensity_zero (C+2)
  have hS' : {n | n+1∈S}.HasDensity 0 :=
    Erdos371CofactorDensity.density_zero_shift (S := S) hS
  apply Erdos371Exploration.density_zero_of_subset
    (T := S∪{n | n+1∈S}) _ (Erdos371CofactorDensity.density_zero_union hS hS')
  intro n hn
  by_contra h
  have h0 : ¬height n≤C+2 := fun hh => h (Or.inl hh)
  have h1 : ¬height (n+1)≤C+2 := fun hh => h (Or.inr hh)
  have hn2 : 2≤n := by
    by_contra hh
    have hh1 : height 1=2 := by decide +kernel
    interval_cases n <;> simp [hh1] at h0
  have hne := adjacent_ne hn2
  change max (amplified n) (amplified (n+1)) ≤
    C*min (amplified n) (amplified (n+1)) at hn
  by_cases hab : height n<height (n+1)
  · have ha := (amplified_lt_iff n (n+1)).mpr hab
    rw [max_eq_right ha.le,min_eq_left ha.le] at hn
    exact (not_le_of_gt (amplification_ratio (by omega : C≤height n) hab)) hn
  · have hba : height (n+1)<height n := by omega
    have hb := (amplified_lt_iff (n+1) n).mpr hba
    rw [max_eq_left hb.le,min_eq_right hb.le] at hn
    exact (not_le_of_gt (amplification_ratio (by omega : C≤height (n+1)) hba)) hn

/-- Both properties used in the proposed dilation argument can hold without
half-density. This is a theorem about general heights, not prime factors. -/
theorem doubling_and_ratio_separation_are_insufficient :
    ∃ f : ℕ → ℕ,
      (∀ n, f (2*n)=f n) ∧
      (∀ n≥2, f (n+1)≠f n) ∧
      (∀ C : ℕ, {n | max (f n) (f (n+1))≤C*min (f n) (f (n+1))}.HasDensity 0) ∧
      ¬{n | f n<f (n+1)}.HasDensity (1/2) :=
  ⟨amplified,amplified_even,fun _ hn => amplified_adjacent_ne hn,
    amplified_fixed_ratio_hasDensity_zero,amplified_not_density_half⟩

end Erdos371AmplifiedDilationObstruction

#print axioms Erdos371AmplifiedDilationObstruction.low_height_hasDensity_zero
#print axioms Erdos371AmplifiedDilationObstruction.doubling_and_ratio_separation_are_insufficient
