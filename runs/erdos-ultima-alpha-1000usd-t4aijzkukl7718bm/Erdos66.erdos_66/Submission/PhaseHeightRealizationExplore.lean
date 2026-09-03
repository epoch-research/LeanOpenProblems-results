import Submission.PhaseCompletePaletteExplore
import Submission.MixedPaletteAssemblyExplore
import Submission.LogarithmicPrefixSystemExplore

/-! Integer mixed step realizations with phases chosen independently for every
piece, after the common finite palette has been fixed. -/
namespace Erdos66PhaseHeightRealization
open Erdos66PhaseCompletePalette Erdos66TranslatedPrefixPalette
  Erdos66MixedPaletteAssembly Erdos66LogarithmicPrefixSystem
  Erdos66LogarithmicStepRealization Erdos66IntegerPaletteAssembly
  Erdos66IntegerPaletteSlices Erdos66IntegerPaletteQuantization
  Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 3200000

section FixedModulus
variable (M : ℕ) [NeZero M]

theorem quantized_two_family_mixed_error {ι : Type*} (s : Finset ι)
    (B : Finset (ZMod M)) (C D : ι → Finset (ZMod M)) (w : ι → ℝ)
    (a b d e : ι → ℕ)
    (hdisj₁ : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hdisj₂ : ∀ i∈s, ∀ j∈s, i ≠ j → e i ≤ d j ∨ e j ≤ d i)
    (hb : ∀ i∈s, b i ≤ M) (he : ∀ i∈s, e i ≤ M) (hw : ∀ i∈s, 0 ≤ w i)
    (R η : ℝ) (hR : 1 ≤ R) (hη : 0 ≤ η)
    (hcardC : ∀ i∈s, w i*(B.card:ℝ) ≤ (C i).card ∧ ((C i).card:ℝ) ≤ R*w i*B.card)
    (hcardD : ∀ i∈s, w i*(B.card:ℝ) ≤ (D i).card ∧ ((D i).card:ℝ) ≤ R*w i*B.card)
    (hprefix : ∀ i∈s, ∀ j∈s, ∀ z x, x ≤ M →
      |(prefixCount M (C i) (D j) z x:ℝ)-(x:ℝ)/M*actualMean M (C i) (D j)| ≤
        η*actualMean M (C i) (D j)) (n : ℕ) :
    |(pairs (assembled M s C a b) (assembled M s D d e) n:ℝ)-
      actualMean M B B*mixedProfile M s w a b d e n| ≤
      ((1+2*η)*R^2-1)*actualMean M B B*(∑ i∈s, w i)^2 := by
  have hp : pairs (assembled M s C a b) (assembled M s D d e) n =
      ∑ i∈s, ∑ j∈s, pairs (slice M (C i) (a i) (b i)) (slice M (D j) (d j) (e j)) n := by
    rw [assembled,pairs_biUnion_left s _ _ n (slice_pairwiseDisjoint M s C a b hdisj₁)]
    apply Finset.sum_congr rfl
    intro i hi
    exact pairs_biUnion_right s _ _ n (slice_pairwiseDisjoint M s D d e hdisj₂)
  have hp' : (pairs (assembled M s C a b) (assembled M s D d e) n:ℝ) =
      ∑ i∈s, ∑ j∈s, (pairs (slice M (C i) (a i) (b i)) (slice M (D j) (d j) (e j)) n:ℝ) := by
    exact_mod_cast hp
  rw [hp',mixedProfile]
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i∈s, ∑ j∈s,
        |(pairs (slice M (C i) (a i) (b i)) (slice M (D j) (d j) (e j)) n:ℝ)-
          actualMean M B B*(overlap M (a i) (b i) (d j) (e j) n*(w i*w j))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i∈s, ∑ j∈s, ((1+2*η)*R^2-1)*actualMean M B B*(w i*w j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact quantized_slice_error M B (C i) (D j) (w i) (w j) R η
        (hw i hi) (hw j hj) hR hη (hcardC i hi) (hcardD j hj)
        (a i) (b i) (d j) (e j) n (hb i hi) (he j hj) (hprefix i hi j hj)
    _ = _ := by rw [pow_two (∑ i∈s, w i),Finset.sum_mul_sum]; simp only [Finset.mul_sum]


end FixedModulus

/-- The heights and accuracy are fixed first. One list of palette members
then supports every later pair of interval arrangements and independent phases.
This is not a change-of-modulus or an infinite-prefix theorem. -/
theorem exists_universal_phase_height_realizer {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i∈s, 1 ≤ w i) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ hM : NeZero M,
      ∃ C : ι → Finset (ZMod M), ∀ α β : ι → ZMod M, ∀ a b d e : ι → ℕ,
        (∀ i∈s, b i ≤ M) → (∀ i∈s, e i ≤ M) →
        (∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) →
        (∀ i∈s, ∀ j∈s, i ≠ j → e i ≤ d j ∨ e j ≤ d i) →
        ∀ n : ℕ, |(pairs (assembled M s (fun i ↦ shift M (C i) (α i)) a b) (assembled M s (fun i ↦ shift M (C i) (β i)) d e) n:ℝ)/Real.log M-
          c*mixedProfile M s w a b d e n| ≤ δ := by
  have hw0 : ∀ i∈s, 0 ≤ w i := fun i hi ↦ (by linarith [hw i hi])
  let S : ℝ := (∑ i∈s, w i)^2
  have hS : 0 ≤ S := sq_nonneg _
  let t := min 1 (δ/(100*(c+1)*(S+1)))
  have ht : 0<t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have hbudget : 100*t*(c+1)*(S+1) ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0<100*(c+1)*(S+1))).mp
      (min_le_right 1 (δ/(100*(c+1)*(S+1))))
    dsimp [t]
    nlinarith only [hh]
  let W : ℝ := 1+∑ i∈s, w i
  have hWsum : 0 ≤ ∑ i∈s, w i := Finset.sum_nonneg hw0
  have hW : 0<W := by dsimp [W]; linarith
  have hwi : ∀ i∈s, w i ≤ W := by
    intro i hi
    have hh := Finset.single_le_sum hw0 hi
    dsimp [W]
    linarith
  obtain ⟨M,hMN,hM1,hM,B,P,hBpos,hBmem,hfitW,htune,hphase,hprefix,hcover⟩ :=
    exists_fitting_phase_palette c t t t W hc ht ht ht1 ht ht1 hW.le N₀
  letI := hM
  have hfit : ∀ i∈s, w i*(B.card:ℝ) ≤ M :=
    fun i hi ↦ (mul_le_mul_of_nonneg_right (hwi i hi) (Nat.cast_nonneg B.card)).trans hfitW
  have hchoose : ∀ i, ∃ D : Finset (ZMod M), i∈s → D∈P ∧
      w i*(B.card:ℝ) ≤ D.card ∧ (D.card:ℝ) ≤ (1+t)*w i*B.card := by
    intro i
    by_cases hi : i∈s
    · have hlow : (B.card:ℝ) ≤ w i*B.card := le_mul_of_one_le_left (by positivity) (hw i hi)
      obtain ⟨D,hDP,hl,hu⟩ := hcover (w i*B.card) hlow (hfit i hi)
      exact ⟨D,fun _ ↦ ⟨hDP,hl,by nlinarith only [hu]⟩⟩
    · exact ⟨B,fun hh ↦ False.elim (hi hh)⟩
  choose C hC using hchoose
  refine ⟨M,hMN,hM1,hM,C,fun α β a b d e hb he hdisj₁ hdisj₂ n ↦ ?_⟩
  have hraw := quantized_two_family_mixed_error M s B
    (fun i ↦ shift M (C i) (α i)) (fun i ↦ shift M (C i) (β i)) w a b d e hdisj₁ hdisj₂ hb he hw0
    (1+t) t (by linarith) ht.le (fun i hi ↦ by simpa only [shift_card] using (hC i hi).2)
    (fun i hi ↦ by simpa only [shift_card] using (hC i hi).2)
    (fun i hi j hj ↦ hprefix _ (hphase _ (hC i hi).1 (α i))
      _ (hphase _ (hC j hj).1 (β j))) n
  have hlog : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM1)
  have hF := mixedProfile_bounds M s w a b d e hw0 hb n
  have hQ := quantization_factor t ht.le ht1
  have hh := normalized_weighted_error
    (pairs (assembled M s (fun i ↦ shift M (C i) (α i)) a b) (assembled M s (fun i ↦ shift M (C i) (β i)) d e) n) (actualMean M B B)
    (mixedProfile M s w a b d e n) c t ((1+2*t)*(1+t)^2-1) S (Real.log M)
    hlog hF.1 hF.2 ht.le hQ.1 htune.le hraw
  exact hh.trans (precision_budget c δ S t hc hδ hS ht.le ht1 hbudget)


end Erdos66PhaseHeightRealization
