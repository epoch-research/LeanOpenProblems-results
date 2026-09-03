import Submission.IntegerThreeAPBound

/-! A quantitative finite monochromatic three-term theorem obtained from the
verified three-AP-free density bound. -/
namespace Erdos3QuantitativeMonochromaticThreeAP
open Finset Erdos3IntegerThreeAPBound Erdos3PolynomialThreeAPThreshold Erdos3DyadicThreeAPBound
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

noncomputable def colorThreeBound (l : ℕ) : ℕ := 2^(thresholdExponent (l+2))

lemma colorThreeBound_pos (l : ℕ) : 0 < colorThreeBound l := by unfold colorThreeBound; positivity

/-- At most 2^l colors suffice to force a monochromatic three-term progression
below the explicit bound. No infinite-color compactness argument is used. -/
theorem bounded_monochromatic_three_AP {K : Type*} [Fintype K] [Nonempty K]
    (c : ℕ → K) (l : ℕ) (hK : Fintype.card K ≤ 2^l) :
    ∃ a d : ℕ, 0 < d ∧ a+2*d < colorThreeBound l ∧
      c a = c (a+d) ∧ c (a+2*d) = c (a+d) := by
  let N := colorThreeBound l
  have hN : 0 < N := colorThreeBound_pos l
  obtain ⟨k,_,hk⟩ := exists_max_image univ
    (fun k : K ↦ ((range N).filter (fun n ↦ c n = k)).card) univ_nonempty
  let S := (range N).filter (fun n ↦ c n = k)
  have hcount : N ≤ Fintype.card K*S.card := by
    calc
      _ = ∑ k : K, ((range N).filter (fun n ↦ c n = k)).card := by
        simpa only [card_range] using card_eq_sum_card_fiberwise (f := c) (s := range N)
          (t := univ) (fun _ _ ↦ mem_univ _)
      _ ≤ ∑ _k : K, S.card := sum_le_sum (fun k hk' ↦ hk k hk')
      _ = _ := by simp
  have hcount' : N ≤ 2^l*S.card := hcount.trans (Nat.mul_le_mul_right _ hK)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdensity : dyadicDensity l ≤ (S.card : ℝ)/N := by
    unfold dyadicDensity
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2^l) hNpos).mpr
    simpa only [one_mul,mul_one,mul_comm] using (show (N : ℝ) ≤ (2 : ℝ)^l*(S.card : ℝ) by exact_mod_cast hcount')
  have hnot : ¬ ThreeAPFree (S : Set ℕ) := by
    intro hf
    have hh := integer_threeAP_density_bound N l hN S (filter_subset _ _) hf hdensity
    exact (lt_irrefl N) hh
  unfold ThreeAPFree at hnot
  push_neg at hnot
  obtain ⟨a,ha,b,hb,t,ht,he,hab⟩ := hnot
  have hordered : ∃ a b t : ℕ, a ∈ S ∧ b ∈ S ∧ t ∈ S ∧ a < b ∧ a+t = b+b := by
    by_cases hlt : a < b
    · exact ⟨a,b,t,ha,hb,ht,hlt,he⟩
    · exact ⟨t,b,a,ht,hb,ha,by omega,by omega⟩
  obtain ⟨a,b,t,ha,hb,ht,hab,he⟩ := hordered
  let d := b-a
  have hd : 0 < d := by dsimp [d]; omega
  have hmid : a+d = b := by dsimp [d]; omega
  have hend : a+2*d = t := by dsimp [d]; omega
  refine ⟨a,d,hd,?_,?_,?_⟩
  · rw [hend]
    exact mem_range.mp (mem_filter.mp ht).1
  · rw [hmid]
    exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
  · rw [hend,hmid]
    exact (mem_filter.mp ht).2.trans (mem_filter.mp hb).2.symm

#print axioms bounded_monochromatic_three_AP
end Erdos3QuantitativeMonochromaticThreeAP
