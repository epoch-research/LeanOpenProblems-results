import FormalConjecturesUtil
import Submission.SubcriticalRestrictionTransfer

/-! The unsigned mass of the CRT restriction correction. A main-term lower
bound is retained explicitly; this file asserts no signed cancellation. -/

namespace Erdos371UnsignedRestrictionMass

open Finset Erdos371LargeDivisorSignedEnergy Erdos371CRTRestrictionError
open Erdos371SubcriticalPrimePairCancellation (pairs count)
open Erdos371WeightedLargeDivisorEnergy (weight weight_nonneg)
open Erdos371ReflectionRange (semiCount)

noncomputable def mainMass (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1 / (z.1*z.2 : ℕ)

noncomputable def rawMass (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1 * ((count z.1 z.2 N : ℝ)+count z.2 z.1 N)

noncomputable def retainedMass (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1 * (members z.2 z.1 N).card

noncomputable def exceptionMass (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1 * ((excessUp z.2 z.1 N : ℝ)+excessDown z.2 z.1 N)

lemma exceptionMass_nonneg (N : ℕ) : 0 ≤ exceptionMass N := by
  exact sum_nonneg fun z _ => mul_nonneg (weight_nonneg N z.1) (by positivity)

lemma rawMass_eq (N : ℕ) : rawMass N=retainedMass N+exceptionMass N := by
  unfold rawMass retainedMass exceptionMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  rintro ⟨q,p⟩ hz
  obtain ⟨hq,hp,_,_⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
  rw [up_count_split hp q N,down_count_split hp hq N,members_card_split]
  push_cast
  ring

lemma retainedMass_le {N : ℕ} (hN : 1<N) : retainedMass N ≤ N := by
  apply le_trans _ (Erdos371WeightedLargeDivisorEnergy.weighted_member_count_le hN)
  unfold retainedMass
  calc
    _ ≤ ∑ z ∈ ((N+1).primesBelow).product ((N+1).primesBelow),
        weight N z.1*(members z.2 z.1 N).card := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro z _ _
        exact mul_nonneg (weight_nonneg N z.1) (Nat.cast_nonneg _)
    _ = _ := (sum_product' _ _ (fun q p => weight N q*(members p q N).card)).trans sum_comm

lemma pair_weight_sum_le {N : ℕ} (hN : 1<N) :
    (∑ z ∈ pairs N, weight N z.1) ≤ semiCount N := by
  calc
    _ ≤ ∑ _z ∈ pairs N, (1 : ℝ) := by
      apply sum_le_sum
      rintro ⟨q,p⟩ hz
      obtain ⟨hq,hp,_,hprod⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
      exact Erdos371SubcriticalRestrictionTransfer.weight_le_one hN hq
        ((Nat.le_mul_of_pos_right q hp.pos).trans hprod)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul,mul_one]
      exact_mod_cast Erdos371SubcriticalPrimePairCancellation.pairs_card_le N

lemma raw_main_lower {N : ℕ} (hN : 1<N) :
    2*(N : ℝ)*mainMass N ≤ rawMass N+2*semiCount N := by
  have ht (z : ℕ×ℕ) (hz : z ∈ pairs N) :
      2*(N : ℝ)*(weight N z.1/(z.1*z.2 : ℕ)) ≤
        weight N z.1*((count z.1 z.2 N : ℝ)+count z.2 z.1 N)+2*weight N z.1 := by
    obtain ⟨hq,hp,hqp,_⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
    have hc := (Nat.coprime_primes hq hp).mpr hqp.ne
    have h₁ := (abs_le.mp (Erdos371SubcriticalPrimePairCancellation.count_error hq.pos hp.pos hc N)).1
    have h₂ := (abs_le.mp (Erdos371SubcriticalPrimePairCancellation.count_error hp.pos hq.pos hc.symm N)).1
    rw [Nat.mul_comm z.2 z.1] at h₂
    have hh : 2*(N : ℝ)/(z.1*z.2 : ℕ) ≤
        (count z.1 z.2 N : ℝ)+count z.2 z.1 N+2 := by rw [mul_div_assoc]; linarith
    have hm := mul_le_mul_of_nonneg_left hh (weight_nonneg N z.1)
    convert hm using 1 <;> ring
  have hs := sum_le_sum ht
  simp only [sum_add_distrib,← mul_sum] at hs
  change 2*(N : ℝ)*mainMass N ≤ rawMass N+2*(∑ z ∈ pairs N,weight N z.1) at hs
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (pair_weight_sum_le hN) (by norm_num : (0:ℝ) ≤ 2)))

/-- A lower bound for the unsigned correction, not for its signed difference. -/
lemma exception_main_lower {N : ℕ} (hN : 1<N) :
    2*mainMass N-1-2*(semiCount N : ℝ)/N ≤ exceptionMass N/N := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hh := raw_main_lower hN
  rw [rawMass_eq] at hh
  have hb := retainedMass_le hN
  apply (le_div_iff₀ hn).mpr
  field_simp
  nlinarith

end Erdos371UnsignedRestrictionMass

#print axioms Erdos371UnsignedRestrictionMass.exception_main_lower
