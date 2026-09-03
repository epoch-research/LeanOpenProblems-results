import Submission.IntegerPaletteQuantizationExplore

/-! Joint mixed integer estimates for two different spatial profiles assembled
from the same palette. Separate self-flatness is not used as a substitute. -/
namespace Erdos66MixedPaletteAssembly
open Erdos66NatPairAlgebra Erdos66IntegerPaletteSlices Erdos66IntegerPaletteAssembly
  Erdos66IntegerPaletteQuantization Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2800000

variable (M : ℕ) [NeZero M]

noncomputable def mixedProfile {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b d e : ι → ℕ) (n : ℕ) : ℝ :=
  ∑ i∈s, ∑ j∈s, overlap M (a i) (b i) (d j) (e j) n*(w i*w j)

lemma mixedProfile_bounds {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b d e : ι → ℕ) (hw : ∀ i∈s, 0 ≤ w i) (hb : ∀ i∈s, b i ≤ M) (n : ℕ) :
    0 ≤ mixedProfile M s w a b d e n ∧ mixedProfile M s w a b d e n ≤ (∑ i∈s, w i)^2 := by
  constructor
  · exact Finset.sum_nonneg (fun i hi ↦ Finset.sum_nonneg (fun j hj ↦
      mul_nonneg (overlap_bounds M _ _ _ _ _ (hb i hi)).1 (mul_nonneg (hw i hi) (hw j hj))))
  · rw [mixedProfile,pow_two,Finset.sum_mul_sum]
    exact Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun j hj ↦
      mul_le_of_le_one_left (mul_nonneg (hw i hi) (hw j hj)) (overlap_bounds M _ _ _ _ _ (hb i hi)).2))

lemma quantized_slice_error (B C D : Finset (ZMod M)) (u v R η : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hR : 1 ≤ R) (hη : 0 ≤ η)
    (hC : u*(B.card:ℝ) ≤ C.card ∧ (C.card:ℝ) ≤ R*u*B.card)
    (hD : v*(B.card:ℝ) ≤ D.card ∧ (D.card:ℝ) ≤ R*v*B.card)
    (a b d e n : ℕ) (hb : b ≤ M) (he : e ≤ M)
    (hprefix : ∀ z x, x ≤ M →
      |(prefixCount M C D z x:ℝ)-(x:ℝ)/M*actualMean M C D| ≤ η*actualMean M C D) :
    |(pairs (slice M C a b) (slice M D d e) n:ℝ)-
      actualMean M B B*(overlap M a b d e n*(u*v))| ≤
      ((1+2*η)*R^2-1)*actualMean M B B*(u*v) := by
  obtain ⟨hl,hh⟩ := quantized_mean_bracket M B C D u v R hu hv (by linarith) hC hD
  obtain ⟨ho0,ho1⟩ := overlap_bounds M a b d e n hb
  have hround := pairs_slice_error M C D a b d e n hb he η hprefix
  change |(pairs (slice M C a b) (slice M D d e) n:ℝ)-
    overlap M a b d e n*actualMean M C D| ≤ 2*η*actualMean M C D at hround
  have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*η by positivity)
  have hdiff0 : 0 ≤ actualMean M C D-actualMean M B B*(u*v) := sub_nonneg.mpr hl
  have h2 := mul_le_of_le_one_left hdiff0 ho1
  have hquant : |overlap M a b d e n*actualMean M C D-
      actualMean M B B*(overlap M a b d e n*(u*v))| ≤
      (R^2-1)*actualMean M B B*(u*v) := by
    have heq : overlap M a b d e n*actualMean M C D-
        actualMean M B B*(overlap M a b d e n*(u*v)) =
        overlap M a b d e n*(actualMean M C D-actualMean M B B*(u*v)) := by ring
    rw [heq,abs_of_nonneg (mul_nonneg ho0 hdiff0)]
    nlinarith only [h2,hh]
  have htri := abs_sub_le (pairs (slice M C a b) (slice M D d e) n:ℝ)
    (overlap M a b d e n*actualMean M C D)
    (actualMean M B B*(overlap M a b d e n*(u*v)))
  nlinarith only [htri,hround,h1,hquant]

/-- Both interval partitions may be chosen independently. Every cross-pair
uses the actual joint palette estimate. -/
theorem quantized_mixed_assembly_error {ι : Type*} (s : Finset ι)
    (B : Finset (ZMod M)) (C : ι → Finset (ZMod M)) (w : ι → ℝ)
    (a b d e : ι → ℕ)
    (hdisj₁ : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hdisj₂ : ∀ i∈s, ∀ j∈s, i ≠ j → e i ≤ d j ∨ e j ≤ d i)
    (hb : ∀ i∈s, b i ≤ M) (he : ∀ i∈s, e i ≤ M) (hw : ∀ i∈s, 0 ≤ w i)
    (R η : ℝ) (hR : 1 ≤ R) (hη : 0 ≤ η)
    (hcard : ∀ i∈s, w i*(B.card:ℝ) ≤ (C i).card ∧ ((C i).card:ℝ) ≤ R*w i*B.card)
    (hprefix : ∀ i∈s, ∀ j∈s, ∀ z x, x ≤ M →
      |(prefixCount M (C i) (C j) z x:ℝ)-(x:ℝ)/M*actualMean M (C i) (C j)| ≤
        η*actualMean M (C i) (C j)) (n : ℕ) :
    |(pairs (assembled M s C a b) (assembled M s C d e) n:ℝ)-
      actualMean M B B*mixedProfile M s w a b d e n| ≤
      ((1+2*η)*R^2-1)*actualMean M B B*(∑ i∈s, w i)^2 := by
  have hp : pairs (assembled M s C a b) (assembled M s C d e) n =
      ∑ i∈s, ∑ j∈s, pairs (slice M (C i) (a i) (b i)) (slice M (C j) (d j) (e j)) n := by
    rw [assembled,pairs_biUnion_left s _ _ n (slice_pairwiseDisjoint M s C a b hdisj₁)]
    apply Finset.sum_congr rfl
    intro i hi
    exact pairs_biUnion_right s _ _ n (slice_pairwiseDisjoint M s C d e hdisj₂)
  have hp' : (pairs (assembled M s C a b) (assembled M s C d e) n:ℝ) =
      ∑ i∈s, ∑ j∈s, (pairs (slice M (C i) (a i) (b i)) (slice M (C j) (d j) (e j)) n:ℝ) := by
    exact_mod_cast hp
  rw [hp',mixedProfile]
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i∈s, ∑ j∈s,
        |(pairs (slice M (C i) (a i) (b i)) (slice M (C j) (d j) (e j)) n:ℝ)-
          actualMean M B B*(overlap M (a i) (b i) (d j) (e j) n*(w i*w j))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i∈s, ∑ j∈s, ((1+2*η)*R^2-1)*actualMean M B B*(w i*w j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact quantized_slice_error M B (C i) (C j) (w i) (w j) R η
        (hw i hi) (hw j hj) hR hη (hcard i hi) (hcard j hj)
        (a i) (b i) (d j) (e j) n (hb i hi) (he j hj) (hprefix i hi j hj)
    _ = _ := by rw [pow_two (∑ i∈s, w i),Finset.sum_mul_sum]; simp only [Finset.mul_sum]

end Erdos66MixedPaletteAssembly
