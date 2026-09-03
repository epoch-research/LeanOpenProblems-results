import Submission.BohrPowerNormalization

/-! Explicit algebraic sample parameters and radius normalization for spectral
symmetry. The rank cost contains no exponential in an inverse density. -/
namespace Erdos3PolynomialRankSkewSymmetry
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrPowerNormalization
  Erdos3SpectralSkewSymmetry Erdos3CorrelationSifting Erdos3UnlocalizedBilinearExtraction
  Erdos3LocalQuadraticIntegration Erdos3BiasedSkewDifferences
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def tolerance (α ω : ℝ) : ℝ := α*ω/64
noncomputable def walkLength (α ω : ℝ) : ℕ := ⌈2/tolerance α ω⌉₊+1
noncomputable def samplingError (α ω : ℝ) : ℝ := tolerance α ω/(4*((walkLength α ω : ℝ)+1))
noncomputable def samplingCount (α Λ ω : ℝ) : ℕ :=
  ⌈8/(samplingError α ω)^2⌉₊+⌈16/(α*(Λ/2)^4*(samplingError α ω)^2)⌉₊+1
noncomputable def rawRank (α Λ ω : ℝ) : ℕ := spectralSymmetryRank α Λ (samplingCount α Λ ω)
noncomputable def rawRadius (α Λ ω : ℝ) : ℝ := min (tolerance α ω/((rawRank α Λ ω : ℝ)+1)) (1/2)
noncomputable def fixedRadiusRank (α Λ ω : ℝ) : ℕ :=
  (radiusPower (rawRadius α Λ ω)+1)*rawRank α Λ ω

lemma tolerance_pos {α ω : ℝ} (hα : 0 < α) (hω : 0 < ω) : 0 < tolerance α ω := by
  unfold tolerance
  positivity

lemma samplingError_pos {α ω : ℝ} (hα : 0 < α) (hω : 0 < ω) : 0 < samplingError α ω :=
  div_pos (tolerance_pos hα hω) (by positivity)

lemma samplingCount_pos (α Λ ω : ℝ) : 0 < samplingCount α Λ ω := by unfold samplingCount; omega

lemma samplingCount_cost {α Λ ω : ℝ} (hα : 0 < α) (hΛ : 0 < Λ) (hω : 0 < ω) :
    8 ≤ (samplingCount α Λ ω : ℝ)*(samplingError α ω)^2 ∧
    16 ≤ (samplingCount α Λ ω : ℝ)*α*(Λ/2)^4*(samplingError α ω)^2 := by
  have he := samplingError_pos hα hω
  have hleft : 8/(samplingError α ω)^2 ≤ (samplingCount α Λ ω : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [samplingCount,Nat.cast_add,Nat.cast_one]
    have hh : (0 : ℝ) ≤ ⌈16/(α*(Λ/2)^4*(samplingError α ω)^2)⌉₊ := Nat.cast_nonneg _
    linarith
  have hright : 16/(α*(Λ/2)^4*(samplingError α ω)^2) ≤ (samplingCount α Λ ω : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [samplingCount,Nat.cast_add,Nat.cast_one]
    have hh : (0 : ℝ) ≤ ⌈8/(samplingError α ω)^2⌉₊ := Nat.cast_nonneg _
    linarith
  refine ⟨(div_le_iff₀ (sq_pos_of_pos he)).mp hleft,?_⟩
  have hh := (div_le_iff₀ (by positivity : 0 < α*(Λ/2)^4*(samplingError α ω)^2)).mp hright
  nlinarith only [hh]

lemma walk_tail {τ : ℝ} (hτ : 0 < τ) {ℓ : ℕ} (hℓ : 2/τ ≤ (ℓ : ℝ)) :
    2*(1/2 : ℝ)^(2*ℓ) ≤ τ := by
  have hpowN : ℓ+1 ≤ 2^(2*ℓ) := (Nat.succ_le_of_lt Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide) (by omega : ℓ ≤ 2*ℓ))
  have hpow : (ℓ : ℝ)+1 ≤ (2 : ℝ)^(2*ℓ) := by exact_mod_cast hpowN
  have hh := (div_le_iff₀ hτ).mp hℓ
  calc
    _ = 2/(2 : ℝ)^(2*ℓ) := by rw [div_pow,one_pow]; ring
    _ ≤ 2/((ℓ : ℝ)+1) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    _ ≤ τ := by rw [div_le_iff₀ (by positivity : (0 : ℝ) < ℓ+1)]; nlinarith

lemma chosen_error_bound {α ω : ℝ} (hα : 0 < α) (hω : 0 < ω) :
    periodError (walkLength α ω) (samplingError α ω) (tolerance α ω) ≤ 3*tolerance α ω := by
  have hτ := tolerance_pos hα hω
  have hℓ : 2/tolerance α ω ≤ (walkLength α ω : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [walkLength,Nat.cast_add,Nat.cast_one]
    exact le_add_of_nonneg_right (by norm_num)
  have htail := walk_tail hτ hℓ
  have hsample : 4*(walkLength α ω : ℝ)*samplingError α ω ≤ tolerance α ω := by
    unfold samplingError
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : (0 : ℝ) < 4*((walkLength α ω : ℝ)+1))]
    nlinarith
  unfold periodError
  linarith

lemma rawRadius_pos {α Λ ω : ℝ} (hα : 0 < α) (hω : 0 < ω) : 0 < rawRadius α Λ ω := by
  apply lt_min (div_pos (tolerance_pos hα hω) (by positivity)) (by norm_num)

lemma spectral_rank_antitone {α σ Λ : ℝ} (hα : 0 < α) (hασ : α ≤ σ) (hΛ : 0 < Λ) (n : ℕ) :
    spectralSymmetryRank σ Λ n ≤ spectralSymmetryRank α Λ n := by
  have hσ : 0 < σ := hα.trans_le hασ
  apply Nat.add_le_add
  · apply Nat.floor_mono
    have hh := Real.log_le_log (one_div_pos.mpr hσ)
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hα hασ)
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _))) (by norm_num)
  · apply Nat.ceil_mono
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (mul_pos hΛ hα))
      (pow_le_pow_left₀ (mul_nonneg hΛ.le hα.le) (mul_le_mul_of_nonneg_left hασ hΛ.le) 2)

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Fixed-radius approximate symmetry with explicit rank costs built only from
algebraic functions, logarithms, and integer roundings of inverse parameters. -/
theorem fixed_radius_spectral_symmetry (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {α Λ ω : ℝ} (hα : 0 < α) (hασ : α ≤ density T)
    (hΛ : 0 < Λ) (hmean : Λ ≤ pairSkewBias T F) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ E : Finset (AddChar G ℂ), E.card ≤ fixedRadiusRank α Λ ω ∧
      bohr E (1/2) ⊆ diffBall T 4 ∧ LocallyAdditive (bohr E (1/2) : Set G) F ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ ω := by
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
  obtain ⟨C,hC,hCP,hCadd,hCsym⟩ := exists_spectral_bohr_symmetry T h0 F hF hdiff hΛ hmean
    (samplingCount_pos α Λ ω) he.le hτ.le hcost.1 hspec (walkLength α ω) herr
  have hCrank : C.card ≤ rawRank α Λ ω := hC.trans (spectral_rank_antitone hα hασ hΛ _)
  have hr : rawRadius α Λ ω ≤ min (tolerance α ω/((C.card : ℝ)+1)) (1/2) := by
    apply min_le_min _ le_rfl
    exact div_le_div_of_nonneg_left hτ.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hCrank 1)
  obtain ⟨E,hE,hEC⟩ := normalize_bohr_radius C (rawRadius_pos hα hω : 0 < rawRadius α Λ ω)
  have hsub := hEC.trans (bohr_mono C hr)
  refine ⟨E,hE.trans (Nat.mul_le_mul_left _ hCrank),hsub.trans hCP,?_,?_⟩
  · intro x hx y hy hxy
    exact hCadd x (hsub hx) y (hsub hy) (hsub hxy)
  · intro x hx y hy
    apply (hCsym x (hsub hx) y (hsub hy)).trans
    apply (div_le_iff₀ hσ).mpr
    change periodError (walkLength α ω) (samplingError α ω) (tolerance α ω) ≤ 3*(α*ω/64) at hbound
    have hh := mul_le_mul_of_nonneg_right hασ hω.le
    nlinarith

#print axioms fixed_radius_spectral_symmetry
end Erdos3PolynomialRankSkewSymmetry
