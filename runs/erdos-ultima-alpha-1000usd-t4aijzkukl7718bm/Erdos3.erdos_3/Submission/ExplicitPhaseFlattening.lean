import Submission.QuantitativeBiasedQuadraticFlattening

/-! Closed choices of the correlation and precision parameters in local
quadratic flattening. The rank and radius depend only on the initial rank,
radius, bias, target accuracy, and outer stability precision. -/
namespace Erdos3ExplicitPhaseFlattening
open Finset Erdos3QuantitativeBiasedQuadraticFlattening Erdos3PhaseRefinementBudgets
  Erdos3LocalQuadraticInverse Erdos3CorrelationSifting Erdos3FiniteBohr
  Erdos3BohrCovering Erdos3RelativeStableBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

noncomputable def precision (x : ℝ) : ℕ := ⌈1/x⌉₊+1

lemma precision_pos (x : ℝ) : 0 < precision x := by unfold precision; omega

lemma precision_inverse_le {x : ℝ} (hx : 0 < x) : 1/(precision x : ℝ) ≤ x := by
  have hp : (0 : ℝ) < precision x := by exact_mod_cast precision_pos x
  have hh : 1/x ≤ (precision x : ℝ) := by
    calc
      _ ≤ (⌈1/x⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ _ := by simp only [precision,Nat.cast_add,Nat.cast_one]; linarith
  apply (div_le_iff₀ hp).mpr
  have ht := (div_le_iff₀ hx).mp hh
  nlinarith

noncomputable def characterMesh (U : ℝ) : ℕ := ⌈16/U⌉₊+1
noncomputable def characterCorrelation (d : ℕ) (U : ℝ) : ℝ :=
  1/((2*characterMesh U+1 : ℕ) : ℝ)^d

lemma characterCorrelation_pos (d : ℕ) (U : ℝ) : 0 < characterCorrelation d U := by
  unfold characterCorrelation
  positivity

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma characterCorrelation_size (D : Finset (AddChar G ℂ)) {U : ℝ} (hU : 0 < U) :
    (characterCorrelation D.card U)^2 ≤ density (bohr D (U/8)) := by
  let M := characterMesh U
  have hM : 0 < M := by dsimp [M,characterMesh]; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hm : 16/U ≤ (M : ℝ) := by
    calc
      _ ≤ (⌈16/U⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ _ := by dsimp [M,characterMesh]; push_cast; linarith
  have hmesh : 2/(M : ℝ) ≤ U/8 := by
    have hh := (div_le_iff₀ hU).mp hm
    apply (div_le_iff₀ hMR).mpr
    nlinarith
  have hc := (card_bohr_lower D hM).trans
    (Nat.mul_le_mul_left _ (card_le_card (bohr_mono D hmesh)))
  have hcR : (Fintype.card G : ℝ) ≤ ((2*M+1 : ℕ) : ℝ)^(2*D.card)*(bohr D (U/8)).card := by
    exact_mod_cast hc
  have hK : (0 : ℝ) < (2*M+1 : ℕ) := by positivity
  have hpow : 0 < (((2*M+1 : ℕ) : ℝ)^D.card)^2 := by positivity
  have he : (characterCorrelation D.card U)^2*(((2*M+1 : ℕ) : ℝ)^(2*D.card)) = 1 := by
    change (1/((2*M+1 : ℕ) : ℝ)^D.card)^2*((2*M+1 : ℕ) : ℝ)^(2*D.card) = 1
    rw [Nat.mul_comm 2 D.card,pow_mul]
    field_simp
  have hh := mul_le_mul_of_nonneg_left hcR (sq_nonneg (characterCorrelation D.card U))
  rw [← mul_assoc,he,one_mul] at hh
  unfold density
  apply (le_div_iff₀ (show (0 : ℝ) < Fintype.card G by exact_mod_cast Fintype.card_pos)).mpr
  exact hh

noncomputable def derivativePrecision (d : ℕ) (U σ β : ℝ) : ℕ :=
  precision (σ*β*characterCorrelation d U/16)
noncomputable def spectrumPrecision (σ β : ℝ) : ℕ := precision (σ*β^3/512)
noncomputable def innerPrecision (σ β : ℝ) : ℕ := precision (σ*β/16)

noncomputable def explicitBaseRadius (d : ℕ) (R σ β : ℝ) (o : ℕ) : ℝ :=
  baseRadiusLower d R o
    (derivativePrecision d (R/(windowDenominator d o : ℝ)) σ β) (spectrumPrecision σ β)
noncomputable def explicitStepRadius (d : ℕ) (R σ β : ℝ) (o : ℕ) : ℝ :=
  stepRadiusLower d R σ β o
    (derivativePrecision d (R/(windowDenominator d o : ℝ)) σ β)
    (spectrumPrecision σ β) (innerPrecision σ β)

lemma explicitBaseRadius_pos (d : ℕ) {R σ β : ℝ} (hR : 0 < R)
    {o : ℕ} (ho : 0 < o) : 0 < explicitBaseRadius d R σ β o :=
  baseRadiusLower_pos d hR ho (precision_pos _) (precision_pos _)

lemma explicitStepRadius_pos (d : ℕ) {R σ β : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hβ : 0 < β)
    {o : ℕ} (ho : 0 < o) : 0 < explicitStepRadius d R σ β o :=
  stepRadiusLower_pos d hR hσ hβ ho (precision_pos _) (precision_pos _) (precision_pos _)

/-- Fully specified parameter choices for one biased local quadratic phase.
The only outer-window assumption is sufficiently fine relative stability. -/
theorem explicit_biased_quadratic_flattening (D : Finset (AddChar G ℂ))
    {R β σ : ℝ} (hR : 0 < R) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) {o : ℕ} (ho : 0 < o)
    (hst : RelativeStable D o R) (hoB : 1/(o : ℝ) ≤ β/8)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    (hbias : β ≤ ‖𝔼 x : bohr D R, q x‖) :
    ∃ E : Finset (AddChar G ℂ), ∃ s t : ℝ, ∃ b ∈ bohr D R,
      (E.card : ℝ) ≤ 32/β^2 ∧ ((D ∪ E).card : ℝ) ≤ D.card+32/β^2 ∧
      explicitBaseRadius D.card R σ β o ≤ s ∧ explicitStepRadius D.card R σ β o ≤ t ∧
      0 < s ∧ 0 < t ∧
      (∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, (b+x)+y ∈ bohr D R) ∧
      (∀ y ∈ bohr (D ∪ E) t, ‖q (b+y)-q b‖ ≤ σ/2) ∧
      ∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, ‖q ((b+x)+y)-q (b+x)‖ ≤ σ := by
  let U := relativeWidth D o R
  let ρ := characterCorrelation D.card U
  let v := derivativePrecision D.card U σ β
  let z := spectrumPrecision σ β
  let w := innerPrecision σ β
  have hρ : 0 < ρ := characterCorrelation_pos _ _
  have hvB : 1/((v : ℝ)*ρ) ≤ σ*β/16 := by
    have hh := precision_inverse_le (show 0 < σ*β*ρ/16 by positivity)
    change 1/(v : ℝ) ≤ σ*β*ρ/16 at hh
    rw [← div_div]
    apply (div_le_iff₀ hρ).mpr
    convert hh using 1 <;> ring
  exact quantitative_biased_quadratic_flattening D hR hβ hβ1 hσ hσ1 hρ
    ho (precision_pos _) (precision_pos _) (precision_pos _) hst
    (characterCorrelation_size D (relativeWidth_pos D ho hR)) hoB hvB
    (precision_inverse_le (show 0 < σ*β^3/512 by positivity))
    (precision_inverse_le (show 0 < σ*β/16 by positivity)) q hq hquad hbias

#print axioms characterCorrelation_size
#print axioms explicit_biased_quadratic_flattening
end Erdos3ExplicitPhaseFlattening
