import Submission.GraphSkewAnnihilation

/-! An averaged skew bias yields a large set of individually biased differences.
Combining with graph sampling gives uniform cross-antisymmetry control. -/
namespace Erdos3BiasedSkewDifferences
open Finset Erdos3FiniteFourier Erdos3AntidiagonalTwistedEnergy
  Erdos3AveragedAntisymmetry Erdos3GraphSkewAnnihilation
  Erdos3CorrelationSifting Erdos3PopularAlmostPeriods
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def normalizedSkewBias (T : Finset G) (F : G → AddChar G ℂ) (d : G) : ℝ :=
  ‖𝔼 x : T, skewPhase F x d‖
noncomputable def pairSkewBias (T : Finset G) (F : G → AddChar G ℂ) : ℝ :=
  𝔼 u : T, 𝔼 v : T, normalizedSkewBias T F ((u : G)-v)

lemma normalizedSkewBias_le_one (T : Finset G) (F : G → AddChar G ℂ) (d : G) :
    normalizedSkewBias T F d ≤ 1 := by
  unfold normalizedSkewBias
  rw [← graphSkewCharacter_mean]
  exact norm_meanChar_le_one _ _

lemma averageSkewBias_eq_normalized (T : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) :
    averageSkewBias T F = (density T)^3*pairSkewBias T F := by
  letI : Nonempty T := hT.to_subtype
  have hσ : 0 < density T := density_pos T hT
  have hform : averageSkewBias T F =
      𝔼 u : G, indicator T u*(𝔼 v : G, indicator T v*‖localSkewBias T F (u-v)‖) := by
    simp only [mul_expect]
    apply expect_congr rfl
    intro u _
    apply expect_congr rfl
    intro v _
    by_cases hu : u ∈ T <;> by_cases hv : v ∈ T <;> simp [indicator,hu,hv]
  rw [hform,expect_indicator_mul T hT]
  simp_rw [expect_indicator_mul T hT,localSkewBias_eq_mean T hT,norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show (0 : ℝ) ≤ (T.card : ℝ)/(Fintype.card G : ℝ) by positivity)]
  change density T*(𝔼 u : T, density T*(𝔼 v : T, density T*normalizedSkewBias T F ((u : G)-v))) = _
  simp only [← mul_expect]
  unfold pairSkewBias
  ring

lemma difference_indicator_mean_le (T D : Finset G) (u : G) :
    (𝔼 v : T, if u-(v : G) ∈ D then (1 : ℝ) else 0) ≤ (D.card : ℝ)/(T.card : ℝ) := by
  let V : Finset T := univ.filter (fun v ↦ u-(v : G) ∈ D)
  have hc : V.card ≤ D.card := by
    apply card_le_card_of_injOn (fun v : T ↦ u-(v : G))
      (fun v hv ↦ (mem_filter.mp hv).2)
    intro a _ b _ hab
    exact Subtype.ext (sub_right_injective hab)
  have he : (𝔼 v : T, if u-(v : G) ∈ D then (1 : ℝ) else 0) = (V.card : ℝ)/(T.card : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card,Fintype.card_coe]
    congr 1
    simp only [V,card_filter]
    norm_cast
  rw [he]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- A bounded average over differences produces many individually good differences.
The cardinality estimate uses the bound |T| on each difference multiplicity. -/
theorem exists_biased_differences (T : Finset G) (hT : T.Nonempty) (b : G → ℝ)
    (hb : ∀ d, b d ≤ 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (hmean : Λ ≤ 𝔼 u : T, 𝔼 v : T, b ((u : G)-v)) :
    ∃ D : Finset G, D.Nonempty ∧ D ⊆ T-T ∧
      Λ*(T.card : ℝ) ≤ 2*(D.card : ℝ) ∧ ∀ d ∈ D, Λ/2 ≤ b d := by
  letI : Nonempty T := hT.to_subtype
  let D := (T-T).filter (fun d ↦ Λ/2 ≤ b d)
  have hbound : (𝔼 u : T, 𝔼 v : T, b ((u : G)-v)) ≤ Λ/2+(D.card : ℝ)/(T.card : ℝ) := by
    apply expect_le univ_nonempty
    intro u _
    calc
      _ ≤ 𝔼 v : T, (Λ/2+(if (u : G)-v ∈ D then (1 : ℝ) else 0)) := by
        apply expect_le_expect
        intro v _
        by_cases hd : (u : G)-v ∈ D
        · rw [if_pos hd]
          linarith [hb ((u : G)-v)]
        · rw [if_neg hd,add_zero]
          have hnot : ¬ Λ/2 ≤ b ((u : G)-v) := by
            intro h
            exact hd (mem_filter.mpr ⟨sub_mem_sub u.property v.property,h⟩)
          exact (lt_of_not_ge hnot).le
      _ = Λ/2+(𝔼 v : T, if (u : G)-v ∈ D then (1 : ℝ) else 0) := by
        rw [expect_add_distrib,Fintype.expect_const]
      _ ≤ _ := add_le_add le_rfl (difference_indicator_mean_le T D u)
  have hc : Λ*(T.card : ℝ) ≤ 2*(D.card : ℝ) := by
    have hh : Λ/2 ≤ (D.card : ℝ)/(T.card : ℝ) := by linarith [hmean.trans hbound]
    have hTR : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hh' := (le_div_iff₀ hTR).mp hh
    linarith
  have hD : D.Nonempty := by
    apply card_pos.mp
    have hh : (0 : ℝ) < D.card := by
      have hp : 0 < Λ*(T.card : ℝ) := mul_pos hΛ (by exact_mod_cast hT.card_pos)
      linarith
    exact_mod_cast hh
  exact ⟨D,hD,filter_subset _ _,hc,fun _ hd ↦ (mem_filter.mp hd).2⟩

/-- Large mixed coefficients produce a large family of genuinely biased skew phases. -/
theorem large_coefficients_biased_differences (T : Finset G) (hT : T.Nonempty)
    (u v : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ t ∈ T, κ ≤ ‖Erdos3TwistedCorrelationEnergy.mixedCoefficient u v F t‖^2) :
    ∃ D : Finset G, D.Nonempty ∧ D ⊆ T-T ∧
      (κ^8*(density T)^4)*(T.card : ℝ) ≤ 2*(D.card : ℝ) ∧
      ∀ d ∈ D, κ^8*(density T)^4/2 ≤ normalizedSkewBias T F d := by
  have hmean := large_coefficients_average_bias_lower T hT u v F hu hv hF hκ.le hc
  change κ^8*(density T)^7 ≤ averageSkewBias T F at hmean
  rw [averageSkewBias_eq_normalized T hT F] at hmean
  have hσ : 0 < density T := density_pos T hT
  have hp : κ^8*(density T)^4 ≤ pairSkewBias T F := by
    apply (mul_le_mul_iff_right₀ (pow_pos hσ 3)).mp
    calc
      _ = κ^8*(density T)^7 := by ring
      _ ≤ _ := hmean
      _ = _ := by ring
  exact exists_biased_differences T hT (normalizedSkewBias T F)
    (normalizedSkewBias_le_one T F) (by positivity) hp

/-- Quantitative cross-antisymmetry: all differences of X almost annihilate
all biased differences in D. This is not yet symmetry on a common Bohr domain. -/
theorem exists_cross_skew_control (T : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {Λ : ℝ} (hΛ : 0 < Λ) (hmean : Λ ≤ pairSkewBias T F)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    (hcost : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*(Λ/2)^4*ε^2) :
    ∃ X D : Finset G, X.Nonempty ∧ D.Nonempty ∧ X ⊆ T ∧ D ⊆ T-T ∧
      T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card ∧
      Λ*(T.card : ℝ) ≤ 2*(D.card : ℝ) ∧
      ∀ s ∈ X, ∀ t ∈ X, ∀ d ∈ D, ‖skewPhase F (s-t) d-1‖ ≤ ε := by
  obtain ⟨D,hD,hDsub,hDsize,hbias⟩ := exists_biased_differences T hT
    (normalizedSkewBias T F) (normalizedSkewBias_le_one T F) hΛ hmean
  obtain ⟨X,hX,hXsub,hXsize,hper⟩ := exists_biased_skew_annihilators T hT F hF hn
    (div_pos hΛ (by norm_num)) hε hcost
  exact ⟨X,D,hX,hD,hXsub,hDsub,hXsize,hDsize,
    fun s hs t ht d hd ↦ hper s hs t ht d (hbias d hd)⟩

#print axioms large_coefficients_biased_differences
#print axioms exists_cross_skew_control
end Erdos3BiasedSkewDifferences
