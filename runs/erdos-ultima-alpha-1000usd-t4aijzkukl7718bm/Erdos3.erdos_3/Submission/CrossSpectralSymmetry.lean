import Submission.PolynomialRankSkewSymmetry

/-! Common spectral periods give symmetry between a small Bohr set and every
biased difference. A Bogolyubov intersection keeps the small set in 2T-2T. -/
namespace Erdos3CrossSpectralSymmetry
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3CorrelationSifting
  Erdos3BiasedSkewDifferences Erdos3CommonCubicBohrPeriods Erdos3TripleCenterSymmetry
  Erdos3UnlocalizedBilinearExtraction Erdos3LocalQuadraticIntegration Erdos3LocalSkewSymmetry
  Erdos3AntidiagonalTwistedEnergy Erdos3SpectralSkewSymmetry Erdos3PolynomialRankSkewSymmetry
  Erdos3BohrPowerNormalization
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma exists_cross_spectral_bohr (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {Λ : ℝ} (hΛ : 0 < Λ) (hΛ1 : Λ ≤ 1)
    {n : ℕ} (hn : 0 < n) {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hL2 : 8 ≤ (n : ℝ)*ε^2)
    (hspec : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*(Λ/2)^4*ε^2)
    (ℓ : ℕ) (herr : periodError ℓ ε τ < density T) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ spectralSymmetryRank (density T) Λ n ∧
      let r := min (τ/((C.card : ℝ)+1)) (1/2)
      bohr C r ⊆ diffBall T 2 ∧
      ∀ x ∈ bohr C r, ∀ d : G, Λ/2 ≤ normalizedSkewBias T F d →
        ‖F x d-F d x‖ ≤ 2*periodError ℓ ε τ/density T := by
  have hT : T.Nonempty := ⟨0,h0⟩
  have hσ := density_pos T hT
  obtain ⟨X,E,hX,_,hXsize,hE,hscalar,hphase⟩ := exists_common_cubic_bohr_periods T h0 F hF hdiff hn
    (div_pos hΛ (by norm_num)) hε hτ hL2 hspec ℓ
  have hcontrol := common_periods_force_skew T h0 F hF (bohr E (τ/((E.card : ℝ)+1))) herr hscalar hphase
  obtain ⟨J,hJ,_,hJsub⟩ := Erdos3FiniteBogolyubov.bogolyubov T hT
  let C := E ∪ J
  let r := min (τ/((C.card : ℝ)+1)) (1/2)
  have hCE : bohr C r ⊆ bohr E (τ/((E.card : ℝ)+1)) := by
    intro x hx
    apply mem_bohr.mpr
    intro χ hχ
    apply (mem_bohr.mp hx χ (mem_union_left _ hχ)).trans
    apply (min_le_left _ _).trans
    exact div_le_div_of_nonneg_left hτ (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (card_le_card (subset_union_left : E ⊆ E ∪ J)) 1)
  have hCJ : bohr C r ⊆ bohr J (1/2) := by
    intro x hx
    exact mem_bohr.mpr (fun χ hχ ↦ (mem_bohr.mp hx χ (mem_union_right _ hχ)).trans (min_le_right _ _))
  have hEcard : E.card ≤ sampleRank (density T) n := hE.trans (sample_log_bound T X hT hX n hXsize)
  have hJbound : (J.card : ℝ) ≤ 32/(Λ*density T)^2 := by
    apply hJ.trans
    have hprod : Λ*density T ≤ density T := by nlinarith
    calc
      _ ≤ 8/(Λ*density T)^2 := div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos (mul_pos hΛ hσ)) (pow_le_pow_left₀ (mul_pos hΛ hσ).le hprod 2)
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  have hJcard : J.card ≤ ⌈32/(Λ*density T)^2⌉₊ := by exact_mod_cast hJbound.trans (Nat.le_ceil _)
  refine ⟨C,(card_union_le E J).trans (Nat.add_le_add hEcard hJcard),?_,?_⟩
  · intro x hx
    rw [diffBall_eq]
    exact hJsub (hCJ hx)
  · intro x hx d hd
    rw [← norm_skewPhase_error]
    apply (le_div_iff₀ hσ).mpr
    have hh := hcontrol.2 d hd x (hCE hx)
    nlinarith only [hh]

/-- Polynomial-rank cross symmetry at fixed radius, without restricting the
large direction to the Bohr set. -/
theorem fixed_radius_cross_symmetry (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {α Λ ω : ℝ} (hα : 0 < α) (hασ : α ≤ density T)
    (hΛ : 0 < Λ) (hΛ1 : Λ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ E : Finset (AddChar G ℂ), E.card ≤ fixedRadiusRank α Λ ω ∧
      bohr E (1/2) ⊆ diffBall T 2 ∧
      ∀ x ∈ bohr E (1/2), ∀ d : G, Λ/2 ≤ normalizedSkewBias T F d → ‖F x d-F d x‖ ≤ ω := by
  have hσ : 0 < density T := hα.trans_le hασ
  have hcost := samplingCount_cost hα hΛ hω
  have he := samplingError_pos hα hω
  have hτ := tolerance_pos hα hω
  have hbound := chosen_error_bound hα hω
  have herr : periodError (walkLength α ω) (samplingError α ω) (tolerance α ω) < density T := by
    change periodError (walkLength α ω) (samplingError α ω) (tolerance α ω) ≤ 3*(α*ω/64) at hbound
    have hh := mul_le_mul_of_nonneg_left hω1 hα.le
    nlinarith
  have hspec : 16*(Fintype.card G : ℝ) ≤ (samplingCount α Λ ω : ℝ)*(T.card : ℝ)*
      (Λ/2)^4*(samplingError α ω)^2 := by
    have hh : 16 ≤ (samplingCount α Λ ω : ℝ)*density T*(Λ/2)^4*(samplingError α ω)^2 := by
      apply hcost.2.trans
      gcongr
    have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hp := mul_le_mul_of_nonneg_right hh hN.le
    unfold density at hp
    convert hp using 1 <;> field_simp
  obtain ⟨C,hC,hCP,hCsym⟩ := exists_cross_spectral_bohr T h0 F hF hdiff hΛ hΛ1
    (samplingCount_pos α Λ ω) he.le hτ.le hcost.1 hspec (walkLength α ω) herr
  have hCrank : C.card ≤ rawRank α Λ ω := hC.trans (spectral_rank_antitone hα hασ hΛ _)
  have hr : rawRadius α Λ ω ≤ min (tolerance α ω/((C.card : ℝ)+1)) (1/2) := by
    apply min_le_min _ le_rfl
    exact div_le_div_of_nonneg_left hτ.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hCrank 1)
  obtain ⟨E,hE,hEC⟩ := normalize_bohr_radius C (rawRadius_pos hα hω : 0 < rawRadius α Λ ω)
  have hsub := hEC.trans (bohr_mono C hr)
  refine ⟨E,hE.trans (Nat.mul_le_mul_left _ hCrank),hsub.trans hCP,?_⟩
  intro x hx d hd
  apply (hCsym x (hsub hx) d hd).trans
  apply (div_le_iff₀ hσ).mpr
  change periodError (walkLength α ω) (samplingError α ω) (tolerance α ω) ≤ 3*(α*ω/64) at hbound
  have hh := mul_le_mul_of_nonneg_right hασ hω.le
  nlinarith

#print axioms fixed_radius_cross_symmetry
end Erdos3CrossSpectralSymmetry
