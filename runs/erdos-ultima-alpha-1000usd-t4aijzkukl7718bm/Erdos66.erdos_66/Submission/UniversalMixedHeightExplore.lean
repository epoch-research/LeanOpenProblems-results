import Submission.MixedPaletteAssemblyExplore
import Submission.LogarithmicPrefixSystemExplore

/-! A fixed finite palette realizes mixed counts for every pair of spatial
arrangements of fixed heights. The two arrangements need not agree. -/
namespace Erdos66UniversalMixedHeight
open Erdos66MixedPaletteAssembly Erdos66LogarithmicPrefixSystem Erdos66BoundedWeightPalette
  Erdos66LogarithmicStepRealization Erdos66IntegerPaletteAssembly
  Erdos66SaturatingCyclicFamily Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 3000000

theorem exists_universal_mixed_height_realizer {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i∈s, 1 ≤ w i) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ hM : NeZero M,
      ∃ C : ι → Finset (ZMod M), ∀ a b d e : ι → ℕ,
        (∀ i∈s, b i ≤ M) → (∀ i∈s, e i ≤ M) →
        (∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) →
        (∀ i∈s, ∀ j∈s, i ≠ j → e i ≤ d j ∨ e j ≤ d i) →
        ∀ n : ℕ, |(pairs (assembled M s C a b) (assembled M s C d e) n:ℝ)/Real.log M-
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
  obtain ⟨M,hMN,hM1,hM,B,P,hBpos,hBmem,hfitW,htune,hprefix,hcover⟩ :=
    exists_fitting_prefix_palette c t t t W hc ht ht ht1 ht ht1 hW.le N₀
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
  refine ⟨M,hMN,hM1,hM,C,fun a b d e hb he hdisj₁ hdisj₂ n ↦ ?_⟩
  have hraw := quantized_mixed_assembly_error M s B C w a b d e hdisj₁ hdisj₂ hb he hw0
    (1+t) t (by linarith) ht.le (fun i hi ↦ (hC i hi).2)
    (fun i hi j hj ↦ hprefix _ (hC i hi).1 _ (hC j hj).1) n
  have hlog : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM1)
  have hF := mixedProfile_bounds M s w a b d e hw0 hb n
  have hQ := quantization_factor t ht.le ht1
  have hh := normalized_weighted_error
    (pairs (assembled M s C a b) (assembled M s C d e) n) (actualMean M B B)
    (mixedProfile M s w a b d e n) c t ((1+2*t)*(1+t)^2-1) S (Real.log M)
    hlog hF.1 hF.2 ht.le hQ.1 htune.le hraw
  exact hh.trans (precision_budget c δ S t hc hδ hS ht.le ht1 hbudget)

end Erdos66UniversalMixedHeight
