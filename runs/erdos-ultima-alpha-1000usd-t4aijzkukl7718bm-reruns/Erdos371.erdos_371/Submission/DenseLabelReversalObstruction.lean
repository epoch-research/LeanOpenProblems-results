import FormalConjecturesUtil
import Submission.LargePrimeFactorCount
import Submission.ExactLabelReversal

/-! A positive population cannot be paired by reversing both exact prime
labels within a fixed linear output range. This does not rule out pairing
just the two comparison signs and is not a disproof of Erdős 371. -/

namespace Erdos371DenseLabelReversalObstruction

open Finset Filter Erdos371LargePrimeFactorCount
open scoped Topology

noncomputable def bothLarge (Y N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => Y < Nat.maxPrimeFac n ∧ Y < Nat.maxPrimeFac (n+1))

lemma bothLarge_card_lower (Y N : ℕ) :
    2*largeCount Y N ≤ N+(bothLarge Y N).card+1 := by
  classical
  let A := (range N).filter (fun n => Y < Nat.maxPrimeFac n)
  let B := (range N).filter (fun n => Y < Nat.maxPrimeFac (n+1))
  have hshift : B.card ≤ A.card+1 := by
    have hh : B.card ≤ (insert N A).card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => n+1)
      · intro n hn
        change n ∈ (range N).filter (fun n => Y < Nat.maxPrimeFac (n+1)) at hn
        obtain ⟨hnN,hnP⟩ := mem_filter.mp hn
        change n+1 ∈ insert N A
        by_cases he : n+1=N
        · exact he ▸ mem_insert_self N A
        · apply mem_insert_of_mem
          apply mem_filter.mpr
          exact ⟨mem_range.mpr (by have := mem_range.mp hnN; omega),hnP⟩
      · intro a _ b _ he
        change a+1=b+1 at he
        omega
    exact hh.trans (card_insert_le N A)
  have hsub : A ∪ B ⊆ range N := union_subset (filter_subset _ _) (filter_subset _ _)
  have hc : (A ∪ B).card ≤ N := by simpa using card_le_card hsub
  have he : A ∩ B = bothLarge Y N := by
    ext n
    simp only [A,B,bothLarge,mem_inter,mem_filter]
    tauto
  have hsum := card_union_add_card_inter A B
  rw [he] at hsum
  change 2*B.card ≤ N+(bothLarge Y N).card+1
  omega

/-- This lower bound uses only one-point marginals and the union bound, not
independence of the two endpoints. -/
theorem bothLarge_positive_proportion : ∀ᶠ t : ℕ in atTop,
    (1/400:ℝ) ≤ ((bothLarge (t^4) (t^7)).card:ℝ)/(t^7:ℕ) := by
  have hpow : Tendsto (fun t : ℕ => t^7) atTop atTop :=
    tendsto_pow_atTop (by omega : (7:ℕ)≠0)
  have hsmall := (tendsto_one_div_atTop_nhds_zero_nat.comp hpow).eventually_lt_const
    (show (0:ℝ)<1/400 by norm_num)
  filter_upwards [fourth_seventh_large_proportion, hsmall, eventually_gt_atTop 0]
    with t hlarge hsmall ht
  simp only [Function.comp_def] at hsmall
  have hN : (0:ℝ) < (t^7:ℕ) := Nat.cast_pos.mpr (pow_pos ht _)
  have hlarge' := (le_div_iff₀ hN).mp hlarge
  have hsmall' := (div_lt_iff₀ hN).mp hsmall
  have hc : (2:ℝ)*largeCount (t^4) (t^7) ≤
      (t^7:ℕ)+(bothLarge (t^4) (t^7)).card+1 := by
    exact_mod_cast bothLarge_card_lower (t^4) (t^7)
  apply (le_div_iff₀ hN).mpr
  linarith

noncomputable def obstructed (C N : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => 1<n ∧
    ¬∃ m ≤ C*N, Nat.maxPrimeFac n=Nat.maxPrimeFac (m+1) ∧
      Nat.maxPrimeFac (n+1)=Nat.maxPrimeFac m)

lemma bothLarge_subset_obstructed {C t : ℕ} (ht : C+1 < t) :
    bothLarge (t^4) (t^7) ⊆ obstructed C (t^7) := by
  classical
  intro n hn
  obtain ⟨hnN,hleft,hright⟩ := mem_filter.mp hn
  have ht0 : 0 < t := by omega
  have ht4 : 1 ≤ t^4 := Nat.one_le_pow _ _ ht0
  have hn1 : 1 < n := by
    have hh := Nat.maxPrimeFac_le (n := n)
    omega
  have hlabel : t^8 < Nat.maxPrimeFac n*Nat.maxPrimeFac (n+1) := by
    have hh : (t^4)^2 < Nat.maxPrimeFac n*Nat.maxPrimeFac (n+1) := by nlinarith
    simpa only [← pow_mul] using hh
  have hscale : (C+1)*t^7 < t^8 := by
    have hh := Nat.mul_lt_mul_of_pos_right ht (pow_pos ht0 7)
    simpa only [show (8:ℕ)=7+1 by omega, pow_succ, Nat.mul_comm] using hh
  exact mem_filter.mpr ⟨hnN,hn1,
    Erdos371ExactLabelReversal.no_linear_label_reversal hn1 (mem_range.mp hnN)
      (hscale.trans hlabel)⟩

/-- Exact preservation and reversal of both largest-prime labels cannot
supply partners for all but a vanishing proportion of sources in a linear
range. This says nothing about pairings that preserve only the sign. -/
theorem positive_proportion_obstructed (C : ℕ) : ∀ᶠ t : ℕ in atTop,
    (1/400:ℝ) ≤ ((obstructed C (t^7)).card:ℝ)/(t^7:ℕ) := by
  filter_upwards [bothLarge_positive_proportion, eventually_gt_atTop (C+1)]
    with t ht hCt
  exact ht.trans (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (card_le_card (bothLarge_subset_obstructed hCt)))
    (Nat.cast_nonneg _))

end Erdos371DenseLabelReversalObstruction

#print axioms Erdos371DenseLabelReversalObstruction.bothLarge_positive_proportion
#print axioms Erdos371DenseLabelReversalObstruction.positive_proportion_obstructed
