import FormalConjecturesUtil
import Submission.CRTRestrictionError
import Submission.ElementaryEnergy

/-! Uniform coordinatewise cancellation of the signed CRT restriction
correction. This does not justify summing over a growing family of pairs. -/

namespace Erdos371UniformCRTCorrection

open Finset Filter Erdos371PrimeDiscrepancy Erdos371LargeDivisorSignedEnergy
open Erdos371CRTRestrictionError Erdos371Exploration
open Erdos371SubcriticalPrimePairCancellation (count count_error)
open scoped Topology

lemma restrictedGroup_abs_le_card (p q N : ℕ) :
    |restrictedGroup p q N| ≤ (members p q N).card := by
  calc
    _ ≤ ∑ n ∈ members p q N, |(sign n : ℝ)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [Erdos371ElementaryEnergy.sign_abs]

lemma restrictedGroup_abs_le_smooth {p K : ℕ} (hpK : p ≤ K) (q N : ℕ) :
    |restrictedGroup p q N| ≤
      (((range N).filter (fun n => P n ≤ K)).card : ℝ) := by
  apply (restrictedGroup_abs_le_card p q N).trans
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hnN,hwin,_⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnN,(le_max_left (P n) (P (n+1))).trans
    (hwin.le.trans hpK)⟩

lemma correction_abs_le_raw {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q<p) (N : ℕ) :
    |correction p q N| ≤ (N : ℝ)/(p*q : ℕ)+1 := by
  have hc := (Nat.coprime_primes hp hq).mpr hqp.ne.symm
  have hu := (abs_le.mp (count_error hq.pos hp.pos hc.symm N)).2
  have hd := (abs_le.mp (count_error hp.pos hq.pos hc N)).2
  rw [Nat.mul_comm q p,up_count_split hp q N] at hu
  rw [down_count_split hp hq N] at hd
  push_cast at hu hd
  unfold correction
  push_cast
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (up p q N).card,
    Nat.cast_nonneg (α := ℝ) (down p q N).card,
    Nat.cast_nonneg (α := ℝ) (excessUp p q N),
    Nat.cast_nonneg (α := ℝ) (excessDown p q N)]

lemma correction_abs_cutoff_bound {p q K : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q<p) (hK : 0<K) (N : ℕ) :
    |correction p q N| ≤ 1+
      (((range N).filter (fun n => P n ≤ K)).card : ℝ)+(N : ℝ)/K := by
  by_cases hpK : p ≤ K
  · have hu := group_add_correction_abs_le_one hp hq hqp N
    have hs := restrictedGroup_abs_le_smooth hpK q N
    have ht : |correction p q N| ≤
        |restrictedGroup p q N+correction p q N|+|restrictedGroup p q N| := by
      have hh := abs_add_le (restrictedGroup p q N+correction p q N)
        (-restrictedGroup p q N)
      have he : restrictedGroup p q N+correction p q N+
          -restrictedGroup p q N = correction p q N := by ring
      simpa only [he,abs_neg] using hh
    linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) N) (Nat.cast_nonneg (α := ℝ) K)]
  · have hk : K ≤ p*q := (by omega : K ≤ p).trans (Nat.le_mul_of_pos_right p hq.pos)
    have hd := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) N)
      (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hk)
    have hh := correction_abs_le_raw hp hq hqp N
    linarith [Nat.cast_nonneg (α := ℝ) ((range N).filter (fun n => P n ≤ K)).card]

lemma correction_ratio_cutoff_bound {p q K N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q<p) (hK : 0<K) (hN : 0<N) :
    |correction p q N/N| ≤ 1/(N : ℝ)+
      {n | P n ≤ K}.partialDensity Set.univ N+1/(K : ℝ) := by
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N),
    bounded_maxPrimeFac_partialDensity]
  apply (div_le_div_of_nonneg_right (correction_abs_cutoff_bound hp hq hqp hK N)
    (Nat.cast_nonneg (α := ℝ) N)).trans_eq
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hk : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  field_simp

/-- Each coordinate is `o(N)`, uniformly over all distinct ordered prime
pairs. No aggregate signed estimate follows without further control. -/
theorem uniformly_small_correction (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, p.Prime → q.Prime → q<p →
      |correction p q N/N| < ε := by
  have hthird : 0<ε/3 := by positivity
  obtain ⟨K,hK,hrecip⟩ := ((eventually_gt_atTop 0).and
    (tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hthird))).exists
  have hs := (bounded_maxPrimeFac_hasDensity_zero K).eventually (gt_mem_nhds hthird)
  have hn := tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hthird)
  filter_upwards [hs,hn,eventually_gt_atTop 0] with N hS hN hNpos
  intro p q hp hq hqp
  have hb := correction_ratio_cutoff_bound hp hq hqp hK hNpos
  change 1/(K : ℝ)<ε/3 at hrecip
  change 1/(N : ℝ)<ε/3 at hN
  linarith

end Erdos371UniformCRTCorrection

#print axioms Erdos371UniformCRTCorrection.uniformly_small_correction
