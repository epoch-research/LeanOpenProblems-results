import Submission.RelativeCyclicFamilyExplore
import Submission.OuterCarryProfileExplore

/-! Finite mixed-flat families can include the full residue group. This is
an algebraic step toward eventually removing an old residue restriction;
no integer placement or scale-transition theorem is asserted here. -/
namespace Erdos66SaturatingCyclicFamily
open Erdos66OuterCarryProfile Erdos66RelativeCyclicFamily
open scoped Classical
set_option maxHeartbeats 1200000

variable (M : ℕ) [NeZero M]

noncomputable def actualMean (C D : Finset (ZMod M)) : ℝ :=
  (C.card : ℝ)*D.card/M

lemma cyclicCount_total (C D : Finset (ZMod M)) :
    ∑ z : ZMod M, cyclicCount M C D z = C.card*D.card := by
  simp only [cyclicCount_sum]
  rw [Finset.sum_comm]
  have hin (a : ZMod M) : (∑ z : ZMod M, if a∈C ∧ z-a∈D then 1 else 0) =
      if a∈C then D.card else 0 := by
    rw [←Equiv.sum_comp (Equiv.addRight a)]
    simp only [Equiv.coe_addRight,add_sub_cancel_right]
    by_cases ha : a∈C <;> simp [ha]
  simp_rw [hin]
  simp

lemma actualMean_error (C D : Finset (ZMod M)) (μ E : ℝ)
    (h : ∀ z, |(cyclicCount M C D z : ℝ)-μ| ≤ E) :
    |actualMean M C D-μ| ≤ E := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hs := (Finset.abs_sum_le_sum_abs
    (fun z : ZMod M ↦ (cyclicCount M C D z : ℝ)-μ) Finset.univ).trans
      (Finset.sum_le_sum (fun z hz ↦ h z))
  have he : (∑ z : ZMod M, (cyclicCount M C D z : ℝ)) = (C.card : ℝ)*D.card := by
    exact_mod_cast cyclicCount_total M C D
  simp only [Finset.sum_sub_distrib,he,Finset.sum_const,Finset.card_univ,
    ZMod.card,nsmul_eq_mul] at hs
  unfold actualMean
  rw [div_sub' hM.ne',abs_div,abs_of_pos hM]
  exact (div_le_iff₀ hM).mpr (by nlinarith)

lemma actualMean_nonneg (C D : Finset (ZMod M)) : 0 ≤ actualMean M C D := by
  unfold actualMean
  positivity

lemma normalize_to_actualMean (C D : Finset (ZMod M)) (μ η : ℝ)
    (hμ : 0 ≤ μ) (hη : 0 ≤ η) (hηsmall : η ≤ 1/2)
    (h : ∀ z, |(cyclicCount M C D z : ℝ)-μ| ≤ η*μ) :
    ∀ z, |(cyclicCount M C D z : ℝ)-actualMean M C D| ≤ 4*η*actualMean M C D := by
  have he := actualMean_error M C D μ (η*μ) h
  have hlow := (abs_le.mp he).1
  have hm : μ ≤ 2*actualMean M C D := by
    have hh := mul_le_mul_of_nonneg_right hηsmall hμ
    nlinarith
  intro z
  calc
    _ ≤ |(cyclicCount M C D z : ℝ)-μ|+|μ-actualMean M C D| := abs_sub_le _ _ _
    _ ≤ 2*η*μ := by rw [abs_sub_comm μ]; linarith [h z]
    _ ≤ 4*η*actualMean M C D := by nlinarith [mul_le_mul_of_nonneg_left hm hη]

lemma cyclicCount_full_right (C : Finset (ZMod M)) (z : ZMod M) :
    cyclicCount M C Finset.univ z = C.card := by simp [cyclicCount]

lemma cyclicCount_full_left (D : Finset (ZMod M)) (z : ZMod M) :
    cyclicCount M Finset.univ D z = D.card := by
  rw [cyclicCount_sum,←Equiv.sum_comp (Equiv.subLeft z)]
  simp [Equiv.subLeft_apply]

lemma actualMean_full_right (C : Finset (ZMod M)) :
    actualMean M C Finset.univ = C.card := by
  simp [actualMean,NeZero.ne M]

lemma actualMean_full_left (D : Finset (ZMod M)) :
    actualMean M Finset.univ D = D.card := by
  simp [actualMean,NeZero.ne M]

noncomputable def saturate (H : ℕ) (C : ℕ → Finset (ZMod M)) (i : ℕ) : Finset (ZMod M) :=
  if i ≤ H then C i else Finset.univ

lemma saturate_mono (H : ℕ) (C : ℕ → Finset (ZMod M)) (hC : Monotone C) :
    Monotone (saturate M H C) := by
  intro i j hij
  by_cases hj : j ≤ H
  · simp only [saturate,if_pos hj,if_pos (hij.trans hj)]
    exact hC hij
  · simp only [saturate,if_neg hj]
    exact Finset.subset_univ _

lemma saturate_full (H : ℕ) (C : ℕ → Finset (ZMod M)) :
    saturate M H C (H+1) = Finset.univ := by simp [saturate]

lemma saturate_mixed_flat (H : ℕ) (C : ℕ → Finset (ZMod M)) (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ i ≤ H, ∀ j ≤ H, ∀ z,
      |(cyclicCount M (C i) (C j) z : ℝ)-actualMean M (C i) (C j)| ≤
        η*actualMean M (C i) (C j)) :
    ∀ i j : ℕ, ∀ z,
      |(cyclicCount M (saturate M H C i) (saturate M H C j) z : ℝ)-
        actualMean M (saturate M H C i) (saturate M H C j)| ≤
          η*actualMean M (saturate M H C i) (saturate M H C j) := by
  intro i j z
  by_cases hi : i ≤ H <;> by_cases hj : j ≤ H
  · simpa only [saturate,if_pos hi,if_pos hj] using h i hi j hj z
  · simp only [saturate,if_pos hi,if_neg hj,cyclicCount_full_right,actualMean_full_right,sub_self,abs_zero]
    positivity
  · simp only [saturate,if_neg hi,if_pos hj,cyclicCount_full_left,actualMean_full_left,sub_self,abs_zero]
    positivity
  · simp only [saturate,if_neg hi,if_neg hj,cyclicCount_full_right,actualMean_full_right,sub_self,abs_zero]
    positivity

/-- The sparse levels have a mean coefficient fixed before the arbitrarily
large modulus. The final full level has exactly flat mixed counts with all
of them. Thus the full level is genuinely additional, not a relabeling of
an already dense family. -/
theorem exists_saturating_family (ε : ℝ) (hε : 0 < ε) (H : ℕ) :
    ∃ β : ℝ, 0 < β ∧ ∀ N₀ : ℕ,
      ∃ M : ℕ, N₀ < M ∧ ∃ hM : NeZero M,
        ∃ C : ℕ → Finset (ZMod M), C 0 = ∅ ∧ C (H+1) = Finset.univ ∧ Monotone C ∧
        (∀ i ≤ H, ∀ j ≤ H, ∀ z,
          |(cyclicCount M (C i) (C j) z : ℝ)-β*i*j| ≤ ε*(β*i*j)) ∧
        ∀ i j : ℕ, ∀ z,
          |(cyclicCount M (C i) (C j) z : ℝ)-actualMean M (C i) (C j)| ≤
            ε*actualMean M (C i) (C j) := by
  let η := min (ε/4) (1/4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hηε : 4*η ≤ ε := by have hh := min_le_left (ε/4) (1/4); dsimp [η]; linarith
  obtain ⟨β,hβ,hfamily⟩ := exists_relative_cyclic_family η hη H
  refine ⟨β,hβ,fun N₀ ↦ ?_⟩
  obtain ⟨M,hMN,hM,C,hC0,hCmono,hC⟩ := hfamily N₀
  letI := hM
  refine ⟨M,hMN,hM,saturate M H C,?_,saturate_full M H C,saturate_mono M H C hCmono,?_,?_⟩
  · simpa only [saturate,if_pos (Nat.zero_le H)] using hC0
  · intro i hi j hj z
    simp only [saturate,if_pos hi,if_pos hj]
    exact (hC i hi j hj z).trans (mul_le_mul_of_nonneg_right (by linarith : η ≤ ε) (by positivity))
  · apply saturate_mixed_flat M H C ε hε.le
    intro i hi j hj z
    have hh := normalize_to_actualMean M (C i) (C j) (β*i*j) η (by positivity) hη.le hηsmall
      (hC i hi j hj) z
    exact hh.trans (mul_le_mul_of_nonneg_right hηε (actualMean_nonneg M _ _))

noncomputable def cardWeight (C : Finset (ZMod M)) : ℝ := C.card/Real.sqrt M

lemma cardWeight_nonneg (C : Finset (ZMod M)) : 0 ≤ cardWeight M C := by
  unfold cardWeight
  positivity

lemma cardWeight_mul (C D : Finset (ZMod M)) :
    cardWeight M C*cardWeight M D = actualMean M C D := by
  unfold cardWeight actualMean
  rw [div_mul_div_comm,Real.mul_self_sqrt (Nat.cast_nonneg M)]

lemma cardWeight_full : cardWeight M Finset.univ = Real.sqrt M := by
  unfold cardWeight
  simp only [Finset.card_univ,ZMod.card]
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  apply (div_eq_iff (Real.sqrt_pos.mpr hM).ne').mpr
  exact (Real.mul_self_sqrt hM.le).symm

/-- After outer repetition, the separate lower and upper carry estimates
also hold uniformly when either level is the full residue group. -/
theorem saturating_carry_error (H : ℕ) (C : ℕ → Finset (ZMod M))
    (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ i ≤ H, ∀ j ≤ H, ∀ z,
      |(cyclicCount M (C i) (C j) z : ℝ)-actualMean M (C i) (C j)| ≤
        η*actualMean M (C i) (C j))
    (K : ℕ) [NeZero K] (i j : ℕ) (t : ZMod M) (r : Fin K) :
    let C' := saturate M H C
    let μ := cardWeight M (C' i)*cardWeight M (C' j)
    |(Erdos66IntegerBlock.lower (M*K) (outerLift M K (C' i)) (outerLift M K (C' j))
      (Erdos66CyclicThickening.blockDigit M K t r).val : ℝ)-r.val*μ| ≤
        ((K : ℝ)*η+1+η)*μ ∧
    |(Erdos66IntegerBlock.upper (M*K) (outerLift M K (C' i)) (outerLift M K (C' j))
      (Erdos66CyclicThickening.blockDigit M K t r).val : ℝ)-((K : ℝ)-r.val)*μ| ≤
        ((K : ℝ)*η+1+η)*μ := by
  dsimp only
  rw [cardWeight_mul]
  have hh := outer_carry_error M K (saturate M H C i) (saturate M H C j) t r
    (actualMean M (saturate M H C i) (saturate M H C j))
    (η*actualMean M (saturate M H C i) (saturate M H C j))
    (actualMean_nonneg M _ _) (mul_nonneg hη (actualMean_nonneg M _ _))
    (saturate_mixed_flat M H C η hη h i j t)
  convert hh using 2 <;> ring

end Erdos66SaturatingCyclicFamily
