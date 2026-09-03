import Submission.TripleCenterSymmetry

/-! Spectral symmetry extraction avoids applying Bogolyubov to the exponentially
small sample set. Only its logarithmic density enters the common Bohr rank. -/
namespace Erdos3SpectralSkewSymmetry
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3CorrelationSifting
  Erdos3BiasedSkewDifferences Erdos3CommonCubicBohrPeriods Erdos3TripleCenterSymmetry
  Erdos3UnlocalizedBilinearExtraction Erdos3LocalQuadraticIntegration Erdos3LocalSkewSymmetry
  Erdos3AntidiagonalTwistedEnergy Erdos3QuantitativeSkewSymmetry
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def sampleRank (σ : ℝ) (n : ℕ) : ℕ :=
  ⌊16*(Real.log 2+(n+1 : ℕ)*Real.log (1/σ))⌋₊
noncomputable def spectralSymmetryRank (σ Λ : ℝ) (n : ℕ) : ℕ :=
  sampleRank σ n+⌈32/(Λ*σ)^2⌉₊
noncomputable def periodError (ℓ : ℕ) (ε τ : ℝ) : ℝ :=
  4*(ℓ : ℝ)*ε+τ+2*(1/2 : ℝ)^(2*ℓ)

lemma sample_log_bound (T X : Finset G) (hT : T.Nonempty) (hX : X.Nonempty) (n : ℕ)
    (hsize : T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card) :
    ⌊16*Real.log (1/density X)⌋₊ ≤ sampleRank (density T) n := by
  have hσ := density_pos T hT
  have hα := density_pos X hX
  have hl := density_lower_of_sample_card T X n hsize
  have hinv : 1/density X ≤ 2/(density T)^(n+1) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity) hl
    convert hh using 1 <;> ring
  apply Nat.floor_mono
  have hh := Real.log_le_log (one_div_pos.mpr hα) hinv
  have he : Real.log (2/(density T)^(n+1)) = Real.log 2+(n+1 : ℕ)*Real.log (1/density T) := by
    rw [Real.log_div (by norm_num) (pow_pos hσ _).ne',Real.log_pow,
      Real.log_div (by norm_num) hσ.ne',Real.log_one]
    ring
  rw [he] at hh
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

lemma second_fourfold_skew_error (T D : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hD : D ⊆ diffBall T 1) (z : G) {e : ℝ}
    (hc : ∀ d ∈ D, ‖skewPhase F z d-1‖ ≤ e)
    {w : G} (hw : w ∈ (D+D)-(D+D)) : ‖skewPhase F z w-1‖ ≤ 4*e := by
  have hdiff {a b : G} (ha : a ∈ D) (hb : b ∈ D) : a-b ∈ diffBall T 4 :=
    diffBall_mono T hT (by decide : 2 ≤ 4) (diffBall_sub (hD ha) (hD hb))
  have herr {a b : G} (ha : a ∈ D) (hb : b ∈ D) : ‖skewPhase F z (a-b)-1‖ ≤ 2*e := by
    have hh := (skew_sub_error_right hF z (diffBall_mono T hT (by decide) (hD ha))
      (diffBall_mono T hT (by decide) (hD hb)) (hdiff ha hb)).trans (add_le_add (hc a ha) (hc b hb))
    linarith
  obtain ⟨a,ha,b,hb,c,hc',d,hd,rfl⟩ := mem_fourfold_split D hw
  have hsum : (a-c)+(b-d) ∈ diffBall T 4 := diffBall_add
    (diffBall_sub (hD ha) (hD hc')) (diffBall_sub (hD hb) (hD hd))
  have hh := (skew_add_error_right hF z (hdiff ha hc') (hdiff hb hd) hsum).trans
    (add_le_add (herr ha hc') (herr hb hd))
  linarith

/-- Symmetry rank is logarithmic in the sample-set density. Bogolyubov is
applied only to the polynomial-density family of biased differences. -/
theorem exists_spectral_bohr_symmetry (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {Λ : ℝ} (hΛ : 0 < Λ) (hmean : Λ ≤ pairSkewBias T F)
    {n : ℕ} (hn : 0 < n) {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hL2 : 8 ≤ (n : ℝ)*ε^2)
    (hspec : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*(Λ/2)^4*ε^2)
    (ℓ : ℕ) (herr : periodError ℓ ε τ < density T) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ spectralSymmetryRank (density T) Λ n ∧
      let r := min (τ/((C.card : ℝ)+1)) (1/2)
      bohr C r ⊆ diffBall T 4 ∧ LocallyAdditive (bohr C r : Set G) F ∧
      ∀ x ∈ bohr C r, ∀ y ∈ bohr C r, ‖F x y-F y x‖ ≤ 8*periodError ℓ ε τ/density T := by
  have hT : T.Nonempty := ⟨0,h0⟩
  have hσ := density_pos T hT
  obtain ⟨D,hD,hDT,hDsize,hbias⟩ := exists_biased_differences T hT
    (normalizedSkewBias T F) (normalizedSkewBias_le_one T F) hΛ hmean
  obtain ⟨X,E,hX,_,hXsize,hE,hscalar,hphase⟩ := exists_common_cubic_bohr_periods T h0 F hF hdiff hn
    (div_pos hΛ (by norm_num)) hε hτ hL2 hspec ℓ
  have hcontrol := common_periods_force_skew T h0 F hF (bohr E (τ/((E.card : ℝ)+1))) herr hscalar hphase
  obtain ⟨J,hJ,_,hJsub⟩ := Erdos3FiniteBogolyubov.bogolyubov D hD
  let C := E ∪ J
  let r : ℝ := min (τ/((C.card : ℝ)+1)) (1/2)
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
  have hDlow : Λ*density T/2 ≤ density D := density_lower_of_difference_card T D Λ hDsize
  have hJbound : (J.card : ℝ) ≤ 32/(Λ*density T)^2 := by
    apply hJ.trans
    have hp : 0 < Λ*density T/2 := by positivity
    calc
      _ ≤ 8/(Λ*density T/2)^2 := div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos hp) (pow_le_pow_left₀ hp.le hDlow 2)
      _ = _ := by ring
  have hJcard : J.card ≤ ⌈32/(Λ*density T)^2⌉₊ := by exact_mod_cast hJbound.trans (Nat.le_ceil _)
  have hCP : bohr C r ⊆ diffBall T 4 := hCE.trans hcontrol.1
  refine ⟨C,(card_union_le E J).trans (Nat.add_le_add hEcard hJcard),hCP,?_,?_⟩
  · intro x hx y hy hxy
    exact hF x (hCP hx) y (hCP hy) (hCP hxy)
  · intro x hx y hy
    have hyfour : y ∈ (D+D)-(D+D) := by simpa only [two_nsmul,mem_sub,mem_add] using hJsub (hCJ hy)
    have hb (d : G) (hd : d ∈ D) : ‖skewPhase F x d-1‖ ≤ 2*periodError ℓ ε τ/density T := by
      apply (le_div_iff₀ hσ).mpr
      have hh := hcontrol.2 d (hbias d hd) x (hCE hx)
      nlinarith only [hh]
    rw [← norm_skewPhase_error]
    have hh := second_fourfold_skew_error T D hT F hF (fun _ hd ↦ mem_diffBall_one.mpr (hDT hd)) x hb hyfour
    convert hh using 1 <;> ring

#print axioms exists_spectral_bohr_symmetry
end Erdos3SpectralSkewSymmetry
