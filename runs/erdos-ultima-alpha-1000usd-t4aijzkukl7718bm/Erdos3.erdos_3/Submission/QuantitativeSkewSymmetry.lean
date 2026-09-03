import Submission.LocalSkewSymmetry

/-! A quantitative common Bohr domain of approximate symmetry from a positive
averaged skew bias. The sampling length and rank costs are explicit. -/
namespace Erdos3QuantitativeSkewSymmetry
open Finset Erdos3FiniteBohr Erdos3LocalQuadraticIntegration Erdos3LocalSkewSymmetry
  Erdos3BiasedSkewDifferences Erdos3CorrelationSifting
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def symmetrySamples (σ Λ ε : ℝ) : ℕ :=
  ⌈16/(σ*(Λ/2)^4*(ε/8)^2)⌉₊+1
noncomputable def symmetryRank (σ Λ ε : ℝ) : ℝ :=
  32/σ^(2*(symmetrySamples σ Λ ε+1))+32/(Λ*σ)^2

lemma symmetrySamples_pos (σ Λ ε : ℝ) : 0 < symmetrySamples σ Λ ε := by
  unfold symmetrySamples
  omega

lemma symmetrySamples_cost {σ Λ ε : ℝ} (hσ : 0 < σ) (hΛ : 0 < Λ) (hε : 0 < ε) :
    16 ≤ (symmetrySamples σ Λ ε : ℝ)*σ*(Λ/2)^4*(ε/8)^2 := by
  have hp : 0 < σ*(Λ/2)^4*(ε/8)^2 := by positivity
  have hh : 16/(σ*(Λ/2)^4*(ε/8)^2) ≤ (symmetrySamples σ Λ ε : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [symmetrySamples,Nat.cast_add,Nat.cast_one]
    exact le_add_of_nonneg_right (by norm_num)
  have he := (div_le_iff₀ hp).mp hh
  nlinarith only [he]

lemma density_lower_of_sample_card (T X : Finset G) (n : ℕ)
    (h : T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card) :
    (density T)^(n+1)/2 ≤ density X := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hh : (T.card : ℝ)^n*T.card ≤ 2*(Fintype.card G : ℝ)^n*X.card := by exact_mod_cast h
  unfold density
  rw [div_pow]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2) hN).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hN (n+1))).mpr
  rw [pow_succ,pow_succ]
  nlinarith only [mul_le_mul_of_nonneg_right hh hN.le]

lemma density_lower_of_difference_card (T D : Finset G) (Λ : ℝ)
    (h : Λ*(T.card : ℝ) ≤ 2*(D.card : ℝ)) : Λ*density T/2 ≤ density D := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  unfold density
  apply (le_div_iff₀ hN).mpr
  field_simp
  linarith

/-- A positive averaged bias forces uniform approximate symmetry on a common
Bohr set. Its rank is explicit and independent of the ambient group size. -/
theorem exists_quantitative_bohr_symmetry (B : Finset (AddChar G ℂ))
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (bohr B (1/2) : Set G) F)
    (T : Finset G) (hT : T.Nonempty) (hTsub : T ⊆ bohr B (1/16))
    (hFdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hmean : Λ ≤ pairSkewBias T F) (hε : 0 < ε) :
    ∃ E : Finset (AddChar G ℂ),
      (E.card : ℝ) ≤ symmetryRank (density T) Λ ε ∧
      bohr E (1/2) ⊆ bohr B (1/4) ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ ε := by
  let σ := density T
  let n := symmetrySamples σ Λ ε
  have hσ : 0 < σ := density_pos T hT
  have hn : 0 < n := symmetrySamples_pos σ Λ ε
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hcost : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*(Λ/2)^4*(ε/8)^2 := by
    have hh := symmetrySamples_cost hσ hΛ hε
    change 16 ≤ (n : ℝ)*((T.card : ℝ)/(Fintype.card G : ℝ))*(Λ/2)^4*(ε/8)^2 at hh
    have hh' := mul_le_mul_of_nonneg_right hh hN.le
    convert hh' using 1 <;> field_simp <;> ring
  obtain ⟨X,D,hX,hD,hXT,hDT,hXsize,hDsize,hcross⟩ := exists_cross_skew_control T hT F hFdiff
    hΛ hmean hn (by positivity : 0 ≤ ε/8) hcost
  obtain ⟨E,hE,hsub,hsym⟩ := cross_control_bohr_symmetry B F hF T X D hTsub hX hD hXT hDT hcross
  have hXlow : σ^(n+1)/2 ≤ density X := density_lower_of_sample_card T X n hXsize
  have hDlow : Λ*σ/2 ≤ density D := density_lower_of_difference_card T D Λ hDsize
  have hXpos : 0 < σ^(n+1)/2 := by positivity
  have hDpos : 0 < Λ*σ/2 := by positivity
  have hXrank : 8/(density X)^2 ≤ 32/σ^(2*(n+1)) := by
    calc
      _ ≤ 8/(σ^(n+1)/2)^2 := div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos hXpos) (pow_le_pow_left₀ hXpos.le hXlow 2)
      _ = _ := by rw [div_pow,← pow_mul,mul_comm (n+1) 2]; ring
  have hDrank : 8/(density D)^2 ≤ 32/(Λ*σ)^2 := by
    calc
      _ ≤ 8/(Λ*σ/2)^2 := div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos hDpos) (pow_le_pow_left₀ hDpos.le hDlow 2)
      _ = _ := by ring
  refine ⟨E,hE.trans (add_le_add hXrank hDrank),hsub,?_⟩
  intro x hx y hy
  simpa only [show 8*(ε/8) = ε by ring] using hsym x hx y hy

#print axioms exists_quantitative_bohr_symmetry
end Erdos3QuantitativeSkewSymmetry
