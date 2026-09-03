import Submission.SaturatingCyclicFamilyExplore

/-! Passing from nominal finite convolution levels to actual cardinality
coverage. These are within-modulus statements only. -/
namespace Erdos66ActualCardinalityCoverage
open Erdos66SaturatingCyclicFamily Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 2200000

lemma relative_square_bracket (a b σ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (h : |a^2-b^2| ≤ σ*b^2) :
    (1-σ)*b ≤ a ∧ a ≤ (1+σ)*b := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor
  · apply le_of_sq_le_sq _ ha
    have hm := mul_nonneg (mul_nonneg hσ (sub_nonneg.mpr hσ1)) (sq_nonneg b)
    nlinarith only [hl,hm]
  · apply le_of_sq_le_sq _ (by positivity)
    have hm := mul_nonneg (add_nonneg hσ (sq_nonneg σ)) (sq_nonneg b)
    nlinarith only [hu,hm]

lemma cardWeight_bracket (M : ℕ) [NeZero M] (C : Finset (ZMod M)) (μ σ w : ℝ)
    (hμ : 0 ≤ μ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hw : 0 ≤ w)
    (hself : ∀ z, |(cyclicCount M C C z:ℝ)-μ*w^2| ≤ σ*(μ*w^2)) :
    (1-σ)*(Real.sqrt μ*w) ≤ cardWeight M C ∧
      cardWeight M C ≤ (1+σ)*(Real.sqrt μ*w) := by
  have he := actualMean_error M C C (μ*w^2) (σ*(μ*w^2)) hself
  have hs : (cardWeight M C)^2=actualMean M C C := by rw [pow_two,cardWeight_mul]
  have hw' : (Real.sqrt μ*w)^2=μ*w^2 := by rw [mul_pow,Real.sq_sqrt hμ]
  apply relative_square_bracket _ _ σ (cardWeight_nonneg M C) (by positivity) hσ hσ1
  simpa only [hs,hw'] using he

lemma adjacent_weight_ratio (i ε σ : ℝ) (hi : 0 ≤ i) (hε : 0<ε) (hε1 : ε ≤ 1)
    (hσ : 0 ≤ σ) (hσsmall : σ ≤ ε/16) (hscale : 4 ≤ ε*i) :
    (1+σ)*(i+1) ≤ (1+ε)*(1-σ)*i := by
  have hfirst : i+1 ≤ (1+ε/4)*i := by nlinarith only [hscale]
  have hfactor : (1+σ)*(1+ε/4) ≤ (1+ε)*(1-σ) := by
    have hm := mul_nonneg hσ (sub_nonneg.mpr hε1)
    nlinarith only [hm,hσsmall,hε]
  have hm1 := mul_le_mul_of_nonneg_left hfirst (by linarith : 0 ≤ 1+σ)
  have hm2 := mul_le_mul_of_nonneg_right hfactor hi
  nlinarith only [hm1,hm2]

lemma adjacent_cardinality_ratio (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (μ σ ε : ℝ) (hμ : 0 ≤ μ) (hσ : 0 ≤ σ) (hσsmall : σ ≤ ε/16)
    (hε : 0<ε) (hε1 : ε ≤ 1) (i : ℕ) (hscale : 4 ≤ ε*(i:ℝ))
    (hi : ∀ z, |(cyclicCount M (C i) (C i) z:ℝ)-μ*(i:ℝ)^2| ≤ σ*(μ*(i:ℝ)^2))
    (hi1 : ∀ z, |(cyclicCount M (C (i+1)) (C (i+1)) z:ℝ)-μ*(i+1:ℕ)^2| ≤ σ*(μ*(i+1:ℕ)^2)) :
    ((C (i+1)).card:ℝ) ≤ (1+ε)*(C i).card := by
  have hσ1 : σ ≤ 1 := by linarith
  have hleft := (cardWeight_bracket M (C i) μ σ i hμ hσ hσ1 (by positivity) hi).1
  have hright := (cardWeight_bracket M (C (i+1)) μ σ (i+1:ℕ) hμ hσ hσ1 (by positivity) hi1).2
  have hratio := adjacent_weight_ratio i ε σ (Nat.cast_nonneg _) hε hε1 hσ hσsmall hscale
  have hm := mul_le_mul_of_nonneg_left hratio (Real.sqrt_nonneg μ)
  have hl := mul_le_mul_of_nonneg_left hleft (by linarith : 0 ≤ 1+ε)
  have hweights : cardWeight M (C (i+1)) ≤ (1+ε)*cardWeight M (C i) := by
    push_cast at hright
    nlinarith only [hright,hm,hl]
  unfold cardWeight at hweights
  rw [←mul_div_assoc] at hweights
  exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos M))).mp hweights

lemma indexed_coverage (f : ℕ → ℝ) (I H : ℕ) (hIH : I ≤ H) (R : ℝ) (hR : 1 ≤ R)
    (hI0 : 0 ≤ f I) (hstep : ∀ j, I ≤ j → j<H → f (j+1) ≤ R*f j) :
    ∀ x : ℝ, f I ≤ x → x ≤ f H → ∃ j, I ≤ j ∧ j ≤ H ∧ x ≤ f j ∧ f j ≤ R*x := by
  intro x hxI hxH
  let S := (Finset.Icc I H).filter (fun j ↦ x ≤ f j)
  have hS : S.Nonempty := ⟨H,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hIH,le_rfl⟩,hxH⟩⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S id hS
  obtain ⟨hjI,hjH⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  have hxj := (Finset.mem_filter.mp hj).2
  have hx0 : 0 ≤ x := hI0.trans hxI
  refine ⟨j,hjI,hjH,hxj,?_⟩
  by_cases he : j=I
  · subst j
    exact hxI.trans (le_mul_of_one_le_left hx0 hR)
  · have hjpos : 0<j := by omega
    have hprev : f (j-1)<x := by
      by_contra hh
      have hm : j-1∈S := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,le_of_not_gt hh⟩
      have hbad := hmin (j-1) hm
      change j ≤ j-1 at hbad
      omega
    have hh := hstep (j-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel hjpos] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hprev.le (by linarith))

 theorem linear_family_cardinality_coverage (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (μ σ ε : ℝ) (hμ : 0 ≤ μ) (hσ : 0 ≤ σ) (hσsmall : σ ≤ ε/16)
    (hε : 0<ε) (hε1 : ε ≤ 1) (I H : ℕ) (hIH : I ≤ H) (hscale : 4 ≤ ε*(I:ℝ))
    (hself : ∀ i≤H, ∀ z,
      |(cyclicCount M (C i) (C i) z:ℝ)-μ*(i:ℝ)^2| ≤ σ*(μ*(i:ℝ)^2)) :
    ∀ x : ℝ, ((C I).card:ℝ) ≤ x → x ≤ (C H).card →
      ∃ j, I ≤ j ∧ j ≤ H ∧ x ≤ (C j).card ∧ ((C j).card:ℝ) ≤ (1+ε)*x := by
  apply indexed_coverage (fun j ↦ ((C j).card:ℝ)) I H hIH (1+ε) (by linarith) (by positivity)
  intro j hjI hjH
  have hji : (I:ℝ) ≤ j := by exact_mod_cast hjI
  have hscalej : 4 ≤ ε*(j:ℝ) := hscale.trans (mul_le_mul_of_nonneg_left hji hε.le)
  exact adjacent_cardinality_ratio M C μ σ ε hμ hσ hσsmall hε hε1 j hscalej
    (hself j (by omega)) (hself (j+1) (by omega))

end Erdos66ActualCardinalityCoverage
