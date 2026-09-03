import Submission.RelativeSpectrum

/-! Translation stability turns relative spectrum generators into phase control. -/
namespace Erdos3RelativeSpectrumPhase
open Finset Erdos3RelativeRiesz Erdos3RelativeChang Erdos3RelativeSpectrum
  Erdos3FiniteFourier Erdos3FiniteBohr Erdos3FourierSmoothing Erdos3BohrTranslation
  Erdos3CorrelationSifting Erdos3ChangSpectrum
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2500000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma expect_normalized_mul_complex (C : Finset G) (hC : C.Nonempty) (f : G → ℂ) :
    (𝔼 x : G, (normalized C x : ℂ)*f x) = 𝔼 x : C, f x := by
  have hα : (density C : ℂ) ≠ 0 := by exact_mod_cast (density_pos C hC).ne'
  have he (x : G) : (normalized C x : ℂ)*f x =
      (if x ∈ C then f x else 0)/(density C : ℂ) := by
    by_cases hx : x ∈ C <;>
      simp [normalized, indicator, hx, div_eq_mul_inv, mul_comm]
  simp_rw [he]
  rw [← expect_div, expect_mask C hC]
  field_simp

/-- A character's phase is controlled by translation stability divided by its mean. -/
theorem meanChar_mul_phase_le (C : Finset G) (hC : C.Nonempty)
    (χ : AddChar G ℂ) (y : G) :
    ‖meanChar C χ‖*‖χ y-1‖ ≤
      𝔼 x : G, |normalized C (x+y)-normalized C x| := by
  have hshift : (𝔼 x : G, (normalized C (x+y) : ℂ)*χ (x+y)) = meanChar C χ := by
    unfold meanChar
    rw [← expect_normalized_mul_complex C hC (fun x ↦ χ x)]
    exact Fintype.expect_equiv (Equiv.addRight y) _ _ (fun _ ↦ rfl)
  have he : (𝔼 x : G, ((normalized C (x+y)-normalized C x : ℝ) : ℂ)*χ (x+y)) =
      meanChar C χ*(1-χ y) := by
    simp only [Complex.ofReal_sub, sub_mul, expect_sub_distrib]
    rw [hshift]
    have hh : (𝔼 x : G, (normalized C x : ℂ)*χ (x+y)) = meanChar C χ*χ y := by
      simp_rw [χ.map_add_eq_mul, ← mul_assoc]
      rw [← expect_mul, expect_normalized_mul_complex C hC]
      rfl
    rw [hh]
    ring
  calc
    _ = ‖meanChar C χ*(1-χ y)‖ := by rw [norm_mul, norm_sub_rev]
    _ = ‖𝔼 x : G, ((normalized C (x+y)-normalized C x : ℝ) : ℂ)*χ (x+y)‖ := by rw [he]
    _ ≤ 𝔼 x : G, ‖((normalized C (x+y)-normalized C x : ℝ) : ℂ)*χ (x+y)‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, χ.norm_apply, mul_one]

lemma phase_le_of_large_mean (C : Finset G) (hC : C.Nonempty)
    {ε δ : ℝ} (hε : 0 < ε) (χ : AddChar G ℂ)
    (hχ : ε < ‖meanChar C χ‖) (y : G)
    (hstable : (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ) :
    ‖χ y-1‖ ≤ δ/ε := by
  apply (le_div_iff₀ hε).mpr
  calc
    _ = ε*‖χ y-1‖ := mul_comm ..
    _ ≤ ‖meanChar C χ‖*‖χ y-1‖ := mul_le_mul_of_nonneg_right hχ.le (norm_nonneg _)
    _ ≤ δ := (meanChar_mul_phase_le C hC χ y).trans hstable

lemma subset_prod_phase (D s : Finset (AddChar G ℂ)) (hs : s ⊆ D)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {y : G} (hy : y ∈ bohr D ρ) :
    ‖(∏ χ ∈ s, χ) y-1‖ ≤ (D.card : ℝ)*ρ := by
  rw [AddChar.prod_apply]
  calc
    _ ≤ ∑ χ ∈ s, ‖χ y-1‖ := norm_prod_sub_one_le s _ (fun χ _ ↦ χ.norm_apply y)
    _ ≤ ∑ χ ∈ D, ‖χ y-1‖ := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ norm_nonneg _)
    _ ≤ ∑ _χ ∈ D, ρ := sum_le_sum (fun χ hχ ↦ mem_bohr.mp hy χ hχ)
    _ = _ := by simp

lemma char_div_phase (χ ψ : AddChar G ℂ) (y : G) :
    ‖(χ/ψ) y-1‖ ≤ ‖χ y-1‖+‖ψ y-1‖ := by
  rw [AddChar.div_apply]
  exact (norm_mul_sub_one_le (χ.norm_apply y)).trans_eq
    (congrArg (fun r ↦ ‖χ y-1‖+r) (char_neg_sub_one_norm ψ y))

lemma obstruction_phase (C : Finset G) (hC : C.Nonempty)
    (D : Finset (AddChar G ℂ)) {ε δ ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    {y : G} (hy : y ∈ bohr D ρ)
    (hstable : (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ)
    (χ : AddChar G ℂ) (s t : Finset (AddChar G ℂ)) (hs : s ⊆ D) (ht : t ⊆ D)
    (hbig : ε < ‖meanChar C (((∏ ψ ∈ s, ψ)*χ)/(∏ ψ ∈ t, ψ))‖) :
    ‖χ y-1‖ ≤ δ/ε+2*(D.card : ℝ)*ρ := by
  let a := ∏ ψ ∈ s, ψ
  let b := ∏ ψ ∈ t, ψ
  let ψ := (a*χ)/b
  have he : χ = ψ*(b/a) := by
    dsimp [ψ]
    rw [div_mul_div_cancel, mul_div_cancel_left]
  calc
    _ = ‖ψ y*(b/a) y-1‖ := by rw [← AddChar.mul_apply, ← he]
    _ ≤ ‖ψ y-1‖+‖(b/a) y-1‖ := norm_mul_sub_one_le (ψ.norm_apply y)
    _ ≤ δ/ε+(‖b y-1‖+‖a y-1‖) := add_le_add
      (phase_le_of_large_mean C hC hε ψ hbig y hstable) (char_div_phase b a y)
    _ ≤ δ/ε+((D.card : ℝ)*ρ+(D.card : ℝ)*ρ) := add_le_add le_rfl
      (add_le_add (subset_prod_phase D t ht hρ hy) (subset_prod_phase D s hs hρ hy))
    _ = _ := by ring

/-- Large-spectrum phases are small on a new-generator Bohr set intersected with
any translation-stability window for C. Rank depends only on relative density. -/
theorem exists_relative_spectrum_phase (A C : Finset G)
    (hA : A.Nonempty) (hC : C.Nonempty) (hAC : A ⊆ C)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    {R : ℕ} (hR : 4*Real.log (2/((A.card : ℝ)/C.card))/η^2 < R+1)
    (herr : ε*4^(R+1) ≤ 1) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ spectrum A η ∧ D.card ≤ R ∧
      ∀ {δ ρ : ℝ}, 0 ≤ δ → 0 ≤ ρ → ∀ y ∈ bohr D ρ,
        (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ →
        ∀ χ : AddChar G ℂ, η ≤ ‖meanChar A χ‖ →
          ‖χ y-1‖ ≤ δ/ε+2*(D.card : ℝ)*ρ := by
  obtain ⟨D, hD, hcard, _, hobs⟩ := exists_relative_spectrum_generators
    A C hA hC hAC hη hη1 hε.le hR herr
  refine ⟨D, hD, hcard, ?_⟩
  intro δ ρ hδ hρ y hy hstable χ hχ
  by_cases hχD : χ ∈ D
  · have hc : (1 : ℝ) ≤ D.card := by exact_mod_cast card_pos.mpr ⟨χ,hχD⟩
    have hh := mul_le_mul_of_nonneg_right hc hρ
    have hh' : 0 ≤ δ/ε := div_nonneg hδ hε.le
    have hph := mem_bohr.mp hy χ hχD
    nlinarith
  · obtain ⟨s, hs, t, ht, hbig⟩ := hobs χ (mem_filter.mpr ⟨mem_univ _, hχ⟩) hχD
    exact obstruction_phase C hC D hε hρ hy hstable χ s t hs ht hbig

#print axioms meanChar_mul_phase_le
#print axioms exists_relative_spectrum_phase
end Erdos3RelativeSpectrumPhase
