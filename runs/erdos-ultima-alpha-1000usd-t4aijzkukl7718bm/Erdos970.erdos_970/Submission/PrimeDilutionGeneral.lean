import Submission.PrimeDilution

/-! Arbitrary positive dilution targets from finite sets of large primes.
Only divergence of prime reciprocals and finite product inequalities are used. -/
namespace Erdos970.PrimeDilution
open Finset Real
set_option maxHeartbeats 2000000

lemma exists_large_prime_reciprocal_sum (B : ℕ) (L : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ B ≤ p) ∧ L < ∑ p ∈ S, 1/(p : ℝ) := by
  classical
  by_contra hh
  push_neg at hh
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := L+B)
  · intro n
    exact Set.indicator_nonneg (fun p _ => by positivity) n
  · intro U
    let V := U.filter Nat.Prime
    let S := V.filter (fun p => B ≤ p)
    have hS : ∀ p ∈ S, p.Prime ∧ B ≤ p := by
      intro p hp
      exact ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
    have hbig := hh S hS
    have hsmall : (∑ p ∈ V.filter (fun p => ¬B ≤ p), 1/(p : ℝ)) ≤ B := by
      have hsub : V.filter (fun p => ¬B ≤ p) ⊆ range B := by
        intro p hp
        exact mem_range.mpr (lt_of_not_ge (mem_filter.mp hp).2)
      calc
        _ ≤ ∑ p ∈ range B, 1/(p : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ ∑ _p ∈ range B, (1 : ℝ) := by
          apply sum_le_sum
          intro p hp
          by_cases hz : p = 0
          · simp [hz]
          · have hp0 : 0 < p := Nat.pos_of_ne_zero hz
            exact (div_le_one (by exact_mod_cast hp0)).mpr (by exact_mod_cast hp0)
        _ = B := by simp
    have hsplit := sum_filter_add_sum_filter_not V (fun p => B ≤ p) (fun p => 1/(p : ℝ))
    have he : (∑ p ∈ U, ({p : ℕ | p.Prime}.indicator (fun n => 1/(n : ℝ))) p) =
        ∑ p ∈ V, 1/(p : ℝ) := by
      simp [V,Set.indicator,sum_filter]
    rw [he]
    change (∑ p ∈ S, 1/(p : ℝ)) ≤ L at hbig
    change (∑ p ∈ S, 1/(p : ℝ)) + _ = _ at hsplit
    linarith only [hbig,hsmall,hsplit]

/-- A finite prime product crosses any target in (0,1). The overshoot is at
most 1/B, and the reciprocal sum is bounded explicitly by 2/d. -/
theorem exists_dilution_primes_target (B : ℕ) (hB : 2 ≤ B) (d : ℝ)
    (hd : 0 < d) (hd1 : d < 1) (hBd : 2/(B : ℝ) ≤ d) :
    ∃ R : Finset ℕ, (∀ p ∈ R, p.Prime ∧ B ≤ p) ∧
      d-1/(B : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)) ∧
      (∏ p ∈ R, (1-1/(p : ℝ))) ≤ d ∧
      (∑ p ∈ R, 1/(p : ℝ)) ≤ 2/d := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  obtain ⟨S,hS,hlarge⟩ := exists_large_prime_reciprocal_sum B (1/d)
  have hx (p : ℕ) (hp : p ∈ S) :
      0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 ∧ 1/(p : ℝ) ≤ 1/(B : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    exact ⟨by positivity,(div_le_one hp0).mpr (by exact_mod_cast (hS p hp).1.one_le),
      one_div_le_one_div_of_le hB0 (by exact_mod_cast (hS p hp).2)⟩
  have hprod := product_sum_le_one S (fun p => 1/(p : ℝ))
    (fun p hp => ⟨(hx p hp).1,(hx p hp).2.1⟩)
  have hsum0 : 0 ≤ ∑ p ∈ S, 1/(p : ℝ) := sum_nonneg (fun _ _ => by positivity)
  have hprod' : (∏ p ∈ S, (1-1/(p : ℝ))) ≤ d := by
    have hden : 0 < 1+∑ p ∈ S, 1/(p : ℝ) := by positivity
    apply ((le_div_iff₀ hden).mpr hprod).trans
    apply (div_le_iff₀ hden).mpr
    have hs := mul_le_mul_of_nonneg_left hlarge.le hd.le
    rw [mul_one_div_cancel hd.ne'] at hs
    nlinarith only [hs,hd]
  obtain ⟨R,hR,hRl,hRu⟩ := exists_crossing_product S (fun p => 1/(p : ℝ))
    (1/(B : ℝ)) d hd1 (by positivity) hx hprod'
  refine ⟨R,fun p hp => hS p (hR hp),hRl,hRu,?_⟩
  have hsum := product_sum_le_one R (fun p => 1/(p : ℝ))
    (fun p hp => ⟨(hx p (hR hp)).1,(hx p (hR hp)).2.1⟩)
  have hs0 : 0 ≤ ∑ p ∈ R, 1/(p : ℝ) := sum_nonneg (fun _ _ => by positivity)
  have hlo : d/2 ≤ ∏ p ∈ R, (1-1/(p : ℝ)) := by
    have hBd' : 2 * (1/(B : ℝ)) ≤ d := by simpa only [mul_one_div] using hBd
    linarith only [hRl,hBd']
  have hh := (mul_le_mul_of_nonneg_right hlo (show 0 ≤ 1+∑ p ∈ R, 1/(p : ℝ) by positivity)).trans hsum
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hh,hd]

#print axioms exists_large_prime_reciprocal_sum
#print axioms exists_dilution_primes_target
end Erdos970.PrimeDilution
