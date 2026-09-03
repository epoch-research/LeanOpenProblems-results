import FormalConjecturesUtil
import Submission.CRTRestrictionError
import Submission.WeightedLargeDivisorEnergy

/-! Summing the exact restriction correction below the product cutoff.
Only the combination of the restricted sum and its correction is shown to
have mean zero; neither summand is discarded. -/

namespace Erdos371SubcriticalRestrictionTransfer

open Finset Filter Erdos371LargeDivisorSignedEnergy
open Erdos371CRTRestrictionError
open Erdos371SubcriticalPrimePairCancellation (pairs count)
open Erdos371WeightedLargeDivisorEnergy (weight weight_nonneg)
open Erdos371ReflectionRange (semiCount)
open scoped Topology

noncomputable def restrictedSum (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1 * restrictedGroup z.2 z.1 N

noncomputable def correctionSum (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, weight N z.1 * correction z.2 z.1 N

lemma sum_eq_raw (N : ℕ) : restrictedSum N+correctionSum N =
    ∑ z ∈ pairs N, weight N z.1 * ((count z.1 z.2 N : ℝ)-count z.2 z.1 N) := by
  unfold restrictedSum correctionSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  rintro ⟨q,p⟩ hz
  obtain ⟨hq,hp,_,_⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
  rw [← mul_add,group_add_correction hp hq]

lemma weight_le_one {N q : ℕ} (hN : 1<N) (hq : q.Prime) (hqN : q ≤ N) :
    weight N q ≤ 1 := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  apply (div_le_one hl).mpr
  exact Real.log_le_log (Nat.cast_pos.mpr hq.pos) (Nat.cast_le.mpr hqN)

/-- The sparse CRT error controls a sum WITH its signed correction. -/
theorem sum_abs_le_semiprime_count {N : ℕ} (hN : 1<N) :
    |restrictedSum N+correctionSum N| ≤ semiCount N := by
  rw [sum_eq_raw]
  calc
    _ ≤ ∑ z ∈ pairs N, |weight N z.1 *
        ((count z.1 z.2 N : ℝ)-count z.2 z.1 N)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ pairs N, (1 : ℝ) := by
      apply sum_le_sum
      rintro ⟨q,p⟩ hz
      obtain ⟨hq,hp,hqp,hprod⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
      have hqN : q ≤ N := (Nat.le_mul_of_pos_right q hp.pos).trans hprod
      have hw0 := weight_nonneg N q
      have hw1 := weight_le_one hN hq hqN
      have hc := Erdos371CRTReflectedRoot.difference_abs_le_one hq.pos hp.pos
        ((Nat.coprime_primes hq hp).mpr hqp.ne) N
      rw [abs_mul,abs_of_nonneg hw0]
      exact (mul_le_of_le_one_right hw0 hc).trans hw1
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul,mul_one]
      exact_mod_cast Erdos371SubcriticalPrimePairCancellation.pairs_card_le N

/-- This transfer identity is NOT a mean-zero theorem for `restrictedSum`
alone. Proving cancellation of `correctionSum` would still be necessary. -/
theorem combined_mean_tendsto_zero :
    Tendsto (fun N : ℕ => (restrictedSum N+correctionSum N)/N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    Erdos371ReflectionRange.semiCount_ratio_zero
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 1] with N hN
    change |(restrictedSum N+correctionSum N)/N| ≤ (semiCount N : ℝ)/N
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (sum_abs_le_semiprime_count hN) (Nat.cast_nonneg N)

end Erdos371SubcriticalRestrictionTransfer

#print axioms Erdos371SubcriticalRestrictionTransfer.sum_abs_le_semiprime_count
#print axioms Erdos371SubcriticalRestrictionTransfer.combined_mean_tendsto_zero
