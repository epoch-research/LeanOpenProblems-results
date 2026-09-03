import Submission.PalettePrefixExtensionExplore
import Submission.BoundedWeightPaletteExplore
import Submission.LogarithmicStepRealizationExplore

/-! An unconditional finite extension system whose old palette pieces are
prescribed before new ones are selected. Its modulus remains fixed. -/
namespace Erdos66LogarithmicPrefixSystem
open AdditiveCombinatorics Erdos66PalettePrefixExtension Erdos66BoundedWeightPalette
  Erdos66LogarithmicStepRealization Erdos66IntegerPaletteAssembly
  Erdos66IntegerPaletteQuantization Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 3200000

lemma normalized_weighted_error (X μ F c τ κ S ℓ : ℝ)
    (hℓ : 0<ℓ) (hF : 0 ≤ F) (hFS : F ≤ S) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (htune : |μ/ℓ-c| ≤ τ) (hX : |X-μ*F| ≤ κ*μ*S) :
    |X/ℓ-c*F| ≤ (κ*(c+τ)+τ)*S := by
  have hS : 0 ≤ S := hF.trans hFS
  have hmu : μ/ℓ ≤ c+τ := by have hh := (abs_le.mp htune).2; linarith
  have hround : |X/ℓ-(μ/ℓ)*F| ≤ κ*(c+τ)*S := by
    have hdiv := div_le_div_of_nonneg_right hX hℓ.le
    have he : X/ℓ-(μ/ℓ)*F=(X-μ*F)/ℓ := by ring
    rw [he,abs_div,abs_of_pos hℓ]
    have hh := mul_le_mul_of_nonneg_right hmu (mul_nonneg hκ hS)
    have he' : κ*μ*S/ℓ=κ*(μ/ℓ)*S := by ring
    rw [he'] at hdiv
    nlinarith only [hdiv,hh]
  have htuning : |(μ/ℓ)*F-c*F| ≤ τ*S := by
    rw [←sub_mul,abs_mul,abs_of_nonneg hF]
    exact (mul_le_mul_of_nonneg_right htune hF).trans (mul_le_mul_of_nonneg_left hFS hτ)
  have htri := abs_sub_le (X/ℓ) ((μ/ℓ)*F) (c*F)
  nlinarith only [htri,hround,htuning]

lemma precision_budget (c δ S t : ℝ) (hc : 0<c) (hδ : 0<δ) (hS : 0 ≤ S)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hbudget : 100*t*(c+1)*(S+1) ≤ δ) :
    (((1+2*t)*(1+t)^2-1)*(c+t)+t)*S ≤ δ := by
  have hQ := quantization_factor t ht ht1
  have h1 := mul_le_mul_of_nonneg_right hQ.2
    (mul_nonneg (add_nonneg hc.le ht) hS)
  have h2 := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ 11*t*S by positivity)
  have h3 := mul_nonneg hc.le (mul_nonneg ht hS)
  have h4 : 0 ≤ t*(c+1) := by positivity
  have h5 := mul_nonneg ht hS
  nlinarith only [h1,h2,h3,h4,h5,hbudget]

/-- There are arbitrarily large finite systems in which every admissible old
palette prefix has an extension with the prescribed normalized step-profile
estimate. The chosen old pieces are not reselected by this theorem. -/
theorem exists_logarithmic_prefix_extension_system {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i∈s, 1 ≤ w i) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) :
    ∃ t : ℝ, 0<t ∧ t ≤ 1 ∧ ∀ N₀ : ℕ,
      ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ hM : NeZero M,
        ∃ (B : Finset (ZMod M)) (P : Finset (Finset (ZMod M))),
          0<B.card ∧ B∈P ∧
          (∀ i∈s, w i*(B.card:ℝ) ≤ M) ∧
          (∀ x : ℝ, (B.card:ℝ) ≤ x → x ≤ M →
            ∃ C∈P, x ≤ (C.card:ℝ) ∧ (C.card:ℝ) ≤ (1+t)*x) ∧
          ∀ (old : Finset ι), old ⊆ s →
          ∀ (D : ι → Finset (ZMod M)) (a b : ι → ℕ) (L : ℕ),
            (∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) →
            (∀ i∈s, b i ≤ M) →
            (∀ i∈old, b i ≤ L) → (∀ i∈s, i∉old → L ≤ a i) →
            (∀ i∈old, D i∈P ∧ w i*(B.card:ℝ) ≤ (D i).card ∧
              ((D i).card:ℝ) ≤ (1+t)*w i*B.card) →
            ∃ A : Finset ℕ, A ⊆ Finset.range M ∧ assembled M old D a b ⊆ A ∧
              (∀ x<L, x∈A ↔ x∈assembled M old D a b) ∧
              (∀ n<L, sumRep (A:Set ℕ) n = sumRep (assembled M old D a b:Set ℕ) n) ∧
              ∀ n : ℕ, |(sumRep (A:Set ℕ) n:ℝ)/Real.log M-
                c*weightedProfile M s w a b n| ≤ δ := by
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
  refine ⟨t,ht,ht1,fun N₀ ↦ ?_⟩
  obtain ⟨M,hMN,hM1,hM,B,P,hBpos,hBmem,hfitW,htune,hprefix,hcover⟩ :=
    exists_fitting_prefix_palette c t t t W hc ht ht ht1 ht ht1 hW.le N₀
  letI := hM
  have hfit : ∀ i∈s, w i*(B.card:ℝ) ≤ M :=
    fun i hi ↦ (mul_le_mul_of_nonneg_right (hwi i hi) (Nat.cast_nonneg B.card)).trans hfitW
  refine ⟨M,hMN,hM1,hM,B,P,hBpos,hBmem,hfit,hcover,?_⟩
  intro old hold D a b L hdisj hb hold_end hnew hD
  obtain ⟨A,hAs,hsub,hagree,hreps,hnewF,htrans,hA⟩ :=
    exists_prefix_preserving_quantized_extension M s old hold B P D w a b L
      hw hfit hdisj hb hold_end hnew t t ht.le ht.le hD hcover hprefix
  refine ⟨A,hAs,hsub,hagree,hreps,fun n ↦ ?_⟩
  have hlog : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast hM1)
  have hF := weightedProfile_bounds M s w a b hw0 hb n
  have hQ := quantization_factor t ht.le ht1
  have hh := normalized_weighted_error (sumRep (A:Set ℕ) n) (actualMean M B B)
    (weightedProfile M s w a b n) c t ((1+2*t)*(1+t)^2-1) S (Real.log M)
    hlog hF.1 hF.2 ht.le hQ.1 htune.le (hA n)
  exact hh.trans (precision_budget c δ S t hc hδ hS ht.le ht1 hbudget)

end Erdos66LogarithmicPrefixSystem
