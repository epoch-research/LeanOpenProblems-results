import Submission.RelativeSpectrumPhase
import Submission.AveragedAntisymmetry

/-! Relative spectral packing for a bounded complex weight. A maximal
approximately orthogonal family gives rank O(eta^-2) and covers each large
coefficient by one frequency modulo a character with large window mean. -/
namespace Erdos3WeightedSpectrumPacking
open Finset Erdos3RelativeRiesz Erdos3RelativeSpectrum Erdos3RelativeSpectrumPhase
  Erdos3ChangAnalytic Erdos3ChangSpectrum Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3AveragedAntisymmetry Erdos3FourierSmoothing Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def weightedCoefficient (C : Finset G) (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  𝔼 x : C, f x*χ x

noncomputable def weightedSpectrum (C : Finset G) (f : G → ℂ) (η : ℝ) : Finset (AddChar G ℂ) :=
  univ.filter (fun χ ↦ η ≤ ‖weightedCoefficient C f χ‖)

def ApproxOrthogonal (C : Finset G) (ε : ℝ) (D : Finset (AddChar G ℂ)) : Prop :=
  ∀ χ ∈ D, ∀ ψ ∈ D, χ ≠ ψ → ‖meanChar C (χ/ψ)‖ ≤ ε

/-- Bessel's inequality with a pairwise orthogonality error. The complex
weight is bounded on C; positivity of the weight is not required. -/
theorem weighted_orthogonal_bound (C : Finset G) (hC : C.Nonempty)
    (f : G → ℂ) (hf : ∀ x ∈ C, ‖f x‖ ≤ 1)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 ≤ ε) (herr : ε ≤ η^2/2)
    (D : Finset (AddChar G ℂ)) (hD : ApproxOrthogonal C ε D)
    (hspec : ∀ χ ∈ D, η ≤ ‖weightedCoefficient C f χ‖) :
    (D.card : ℝ) ≤ 2/η^2 := by
  letI : Nonempty C := hC.to_subtype
  choose u hu huRe using (fun χ : AddChar G ℂ ↦ exists_phase (weightedCoefficient C f χ))
  let S : G → ℂ := fun x ↦ ∑ χ ∈ D, u χ*χ x
  have hmean : (D.card : ℝ)*η ≤ (𝔼 x : C, f x*S x).re := by
    have he : (𝔼 x : C, f x*S x).re = ∑ χ ∈ D, ‖weightedCoefficient C f χ‖ := by
      dsimp only [S]
      simp_rw [mul_sum,expect_sum_comm]
      rw [Complex.re_sum]
      apply sum_congr rfl
      intro χ hχ
      have ht : (𝔼 x : C, f x*(u χ*χ x)) = u χ*weightedCoefficient C f χ := by
        unfold weightedCoefficient
        rw [mul_expect]
        apply expect_congr rfl
        intro x _
        ring
      rw [ht,huRe]
    rw [he]
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum hspec
  have hnorm : (D.card : ℝ)*η ≤ ‖𝔼 x : C, f x*S x‖ := hmean.trans (Complex.re_le_norm _)
  have hL2 : (𝔼 x : C, ‖S x‖^2) ≤ (D.card : ℝ)+ε*(D.card : ℝ)^2 := by
    have he := expect_norm_sq_sum_chars_le C hC D (fun χ ↦ χ) u hε
      (fun χ hχ ψ hψ hne ↦ by rw [← meanChar_div]; exact hD χ hχ ψ hψ hne)
    simpa only [S,hu,one_pow,sum_const,nsmul_eq_mul,mul_one] using he
  have hf2 : (𝔼 x : C, ‖f x‖^2) ≤ 1 := by
    apply expect_le univ_nonempty
    intro x _
    have hh := hf x x.property
    nlinarith [norm_nonneg (f x)]
  have hCS := complex_expect_cauchy_schwarz (fun x : C ↦ f x) (fun x : C ↦ S x)
  have hupper : ‖𝔼 x : C, f x*S x‖^2 ≤ (D.card : ℝ)+ε*(D.card : ℝ)^2 := by
    apply hCS.trans
    apply le_trans _ hL2
    exact (mul_le_mul_of_nonneg_right hf2 (expect_nonneg (fun _ _ ↦ sq_nonneg _))).trans_eq (one_mul _)
  have hn : 0 ≤ (D.card : ℝ) := Nat.cast_nonneg _
  have hprod : 0 ≤ (D.card : ℝ)*η := mul_nonneg hn hη.le
  have hs := pow_le_pow_left₀ hprod hnorm 2
  have he := mul_le_mul_of_nonneg_right herr (sq_nonneg (D.card : ℝ))
  apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
  by_cases hz : (D.card : ℝ) = 0
  · rw [hz,zero_mul]; norm_num
  · have hp : 0 < (D.card : ℝ) := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

/-- Maximal pairwise spectral packing. Every large coefficient lies near a
single selected frequency, where nearness is measured by the window mean. -/
theorem exists_weighted_spectrum_cover (C : Finset G) (hC : C.Nonempty)
    (f : G → ℂ) (hf : ∀ x ∈ C, ‖f x‖ ≤ 1)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε < 1) (herr : ε ≤ η^2/2) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ weightedSpectrum C f η ∧
      (D.card : ℝ) ≤ 2/η^2 ∧
      ∀ χ ∈ weightedSpectrum C f η, ∃ ψ ∈ D, ε < ‖meanChar C (χ/ψ)‖ := by
  let S := weightedSpectrum C f η
  let T := S.powerset.filter (ApproxOrthogonal C ε)
  have hT : T.Nonempty := ⟨∅,by simp [T,ApproxOrthogonal]⟩
  obtain ⟨D,hDT,hmax⟩ := exists_max_image T card hT
  have hDsub : D ⊆ S := mem_powerset.mp (mem_filter.mp hDT).1
  have hD : ApproxOrthogonal C ε D := (mem_filter.mp hDT).2
  have hb := weighted_orthogonal_bound C hC f hf hη hε herr D hD
    (fun χ hχ ↦ (mem_filter.mp (hDsub hχ)).2)
  refine ⟨D,hDsub,hb,?_⟩
  intro χ hχ
  by_cases hχD : χ ∈ D
  · refine ⟨χ,hχD,?_⟩
    letI : Nonempty C := hC.to_subtype
    simpa only [div_self',meanChar,AddChar.one_apply,Fintype.expect_const,norm_one] using hε1
  · by_contra hn
    push_neg at hn
    have hext : ApproxOrthogonal C ε (insert χ D) := by
      intro a ha b hb hab
      rcases mem_insert.mp ha with haeq | haD
      · subst a
        rcases mem_insert.mp hb with hbeq | hbD
        · exact (hab hbeq.symm).elim
        · exact hn b hbD
      · rcases mem_insert.mp hb with hbeq | hbD
        · subst b
          rw [norm_meanChar_div_comm]
          exact hn a haD
        · exact hD a haD b hbD hab
    have hTin : insert χ D ∈ T := mem_filter.mpr
      ⟨mem_powerset.mpr (insert_subset hχ hDsub),hext⟩
    have hh := hmax (insert χ D) hTin
    rw [card_insert_of_notMem hχD] at hh
    omega

/-- All weighted large-spectrum phases are controlled on a Bohr set of
rank at most 2/eta^2 intersected with any stability window for C. -/
theorem exists_weighted_spectrum_phase (C : Finset G) (hC : C.Nonempty)
    (f : G → ℂ) (hf : ∀ x ∈ C, ‖f x‖ ≤ 1)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1) (herr : ε ≤ η^2/2) :
    ∃ D : Finset (AddChar G ℂ), (D.card : ℝ) ≤ 2/η^2 ∧
      ∀ {δ γ : ℝ}, ∀ y ∈ bohr D γ,
        (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ →
        ∀ χ : AddChar G ℂ, η ≤ ‖weightedCoefficient C f χ‖ →
          ‖χ y-1‖ ≤ δ/ε+γ := by
  obtain ⟨D,_,hD,hcover⟩ := exists_weighted_spectrum_cover C hC f hf hη hε.le hε1 herr
  refine ⟨D,hD,?_⟩
  intro δ γ y hy hstable χ hχ
  obtain ⟨ψ,hψ,hlarge⟩ := hcover χ (mem_filter.mpr ⟨mem_univ _,hχ⟩)
  have he : χ = (χ/ψ)*ψ := (div_mul_cancel χ ψ).symm
  calc
    _ = ‖(χ/ψ) y*ψ y-1‖ := by rw [← AddChar.mul_apply,← he]
    _ ≤ ‖(χ/ψ) y-1‖+‖ψ y-1‖ := norm_mul_sub_one_le ((χ/ψ).norm_apply y)
    _ ≤ _ := add_le_add (phase_le_of_large_mean C hC hε (χ/ψ) hlarge y hstable)
      (mem_bohr.mp hy ψ hψ)

#print axioms weighted_orthogonal_bound
#print axioms exists_weighted_spectrum_cover
#print axioms exists_weighted_spectrum_phase
end Erdos3WeightedSpectrumPacking
