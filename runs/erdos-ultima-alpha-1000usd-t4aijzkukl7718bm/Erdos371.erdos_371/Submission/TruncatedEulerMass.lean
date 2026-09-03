import Submission.QuadraticResidueSieve

/-! A first-moment bound for the mass retained by a product (logarithmic-cost)
cutoff in a finite Euler product. -/

namespace Erdos371
namespace FiniteSieve
open Finset
variable {ι : Type*} [DecidableEq ι]

noncomputable def weightedSubsetMoment (S : Finset ι) (h c : ι → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (∏ i ∈ T, h i)*(∑ i ∈ T, c i)

lemma weightedSubsetMoment_eq (S : Finset ι) (h c : ι → ℝ)
    (hh : ∀ i ∈ S, 0 ≤ h i) :
    weightedSubsetMoment S h c = (∏ i ∈ S, (1+h i)) * ∑ i ∈ S, c i*h i/(1+h i) := by
  induction S using Finset.induction_on with
  | empty => simp [weightedSubsetMoment]
  | @insert a S ha ih =>
    have hha := hh a (mem_insert_self a S)
    have hhS : ∀ i ∈ S, 0 ≤ h i := fun i hi => hh i (mem_insert_of_mem hi)
    have he : weightedSubsetMoment (insert a S) h c = weightedSubsetMoment S h c +
        h a * (weightedSubsetMoment S h c + c a*(∏ i ∈ S, (1+h i))) := by
      unfold weightedSubsetMoment
      rw [sum_powerset_insert ha]
      congr 1
      rw [prod_one_add,mul_add]
      simp_rw [mul_sum]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro T hT
      have haT := notMem_mono (mem_powerset.mp hT) ha
      rw [prod_insert haT,sum_insert haT]
      ring
    rw [he,ih hhS,prod_insert ha,sum_insert ha]
    have hz : 1+h a ≠ 0 := by linarith
    field_simp
    ring

lemma truncated_subset_mass_lower (S : Finset ι) (h c : ι → ℝ)
    (hh : ∀ i ∈ S, 0 ≤ h i) (hc : ∀ i ∈ S, 0 ≤ c i)
    (L : ℝ) (hL : 0 < L) (hm : (∑ i ∈ S, c i*h i/(1+h i)) ≤ L/2) :
    (∏ i ∈ S, (1+h i))/2 ≤
      ∑ T ∈ S.powerset, if (∑ i ∈ T, c i) ≤ L then ∏ i ∈ T, h i else 0 := by
  let W := ∏ i ∈ S, (1+h i)
  let A := ∑ T ∈ S.powerset, if (∑ i ∈ T, c i) ≤ L then ∏ i ∈ T, h i else 0
  let B := ∑ T ∈ S.powerset, if L < (∑ i ∈ T, c i) then ∏ i ∈ T, h i else 0
  have htot : A+B=W := by
    dsimp only [A,B,W]
    rw [← sum_add_distrib,prod_one_add]
    apply sum_congr rfl
    intro T hT
    by_cases ht : (∑ i ∈ T, c i) ≤ L
    · simp only [if_pos ht,if_neg (not_lt.mpr ht),add_zero]
    · simp only [if_neg ht,if_pos (lt_of_not_ge ht),zero_add]
  have hmarkov : L*B ≤ weightedSubsetMoment S h c := by
    dsimp only [B,weightedSubsetMoment]
    rw [mul_sum]
    apply sum_le_sum
    intro T hT
    have hTS := mem_powerset.mp hT
    have hw : 0 ≤ ∏ i ∈ T, h i := prod_nonneg fun i hi => hh i (hTS hi)
    have hcost : 0 ≤ ∑ i ∈ T, c i := sum_nonneg fun i hi => hc i (hTS hi)
    split_ifs with ht
    · nlinarith
    · simp only [mul_zero]
      exact mul_nonneg hw hcost
  rw [weightedSubsetMoment_eq S h c hh] at hmarkov
  have hW : 0 ≤ W := prod_nonneg fun i hi => by have := hh i hi; linarith
  have hbound := mul_le_mul_of_nonneg_left hm hW
  change W/2 ≤ A
  change L*B ≤ W*(∑ i ∈ S, c i*h i/(1+h i)) at hmarkov
  nlinarith

#print axioms weightedSubsetMoment_eq
#print axioms truncated_subset_mass_lower
end FiniteSieve
end Erdos371
