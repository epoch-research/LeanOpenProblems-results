import Submission.ChangAnalytic
import Submission.PopularAlmostPeriods

/-! Chang's large-spectrum bound via a dissociated Riesz-product L² identity.
This is an auxiliary result and does not settle the original conjecture. -/
namespace Erdos3ChangSpectrum
open Finset Erdos3DissociatedRiesz Erdos3ChangAnalytic
  Erdos3CorrelationSifting Erdos3PopularAlmostPeriods
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def spectrum (A : Finset G) (η : ℝ) : Finset (AddChar G ℂ) :=
  univ.filter (fun χ ↦ η ≤ ‖𝔼 a : A, χ a‖)

lemma exists_phase (z : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ (u*z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · exact exists_unit_phase hz

/-- A dissociated family of characters with large mean on A has logarithmically bounded size. -/
theorem dissociated_spectrum_bound (A : Finset G) (hA : A.Nonempty)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (D : Finset (AddChar G ℂ))
    (hD : MulDissociated (D : Set (AddChar G ℂ)))
    (hspec : ∀ χ ∈ D, η ≤ ‖𝔼 a : A, χ a‖) :
    (D.card : ℝ) ≤ 4*Real.log (1/density A)/η^2 := by
  letI : Nonempty A := hA.to_subtype
  have hα := density_pos A hA
  let c : ℝ := η/4
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ≤ 1/2 := by dsimp [c]; linarith
  choose u hun hure using fun χ : AddChar G ℂ ↦ exists_phase (𝔼 a : A, χ a)
  let a : AddChar G ℂ → ℂ := fun χ ↦ (c : ℂ)*u χ
  have han (χ : AddChar G ℂ) : ‖a χ‖ = c := by
    simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, hun, mul_one,
      abs_of_pos hc]
  have hax (χ : AddChar G ℂ) (x : G) : ‖a χ*χ x‖ = c := by
    rw [norm_mul, han, χ.norm_apply, mul_one]
  let P : G → ℝ := fun x ↦ ∏ χ ∈ D, ‖1+a χ*χ x‖^2
  have hpterm (χ : AddChar G ℂ) (x : G) : 0 < ‖1+a χ*χ x‖^2 := by
    exact sq_pos_of_pos (norm_one_add_pos (by rw [hax]; linarith))
  have hP (x : G) : 0 < P x := prod_pos (fun χ _ ↦ hpterm χ x)
  have hPmean : (𝔼 x : G, P x) = (1+c^2)^D.card := by
    have h := riesz_l2 D hD a
    simpa only [P, norm_prod, prod_pow, han, prod_const] using h
  have hPweighted : density A*(𝔼 x : A, P x) ≤ (1+c^2)^D.card := by
    rw [← expect_indicator_mul A hA, ← hPmean]
    apply expect_le_expect
    intro x _
    by_cases hx : x ∈ A
    · simp only [indicator, if_pos hx, one_mul, le_refl]
    · simp only [indicator, if_neg hx, zero_mul]
      exact (hP x).le
  have hPupper : (𝔼 x : A, P x) ≤ (1+c^2)^D.card / density A := by
    apply (le_div_iff₀ hα).mpr
    nlinarith [hPweighted]
  have hphaseMean (χ : AddChar G ℂ) :
      (𝔼 x : A, (u χ*χ x).re) = ‖𝔼 x : A, χ x‖ := by
    rw [← expect_re, ← mul_expect, hure]
  have hlogterm (χ : AddChar G ℂ) (x : G) :
      2*c*(u χ*χ x).re - 2*c^2 ≤ Real.log (‖1+a χ*χ x‖^2) := by
    have h := log_norm_sq_one_add_lower (by rw [hax]; exact hc2 : ‖a χ*χ x‖ ≤ 1/2)
    rw [hax] at h
    simpa only [a, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h
  have hmeanterm (χ : AddChar G ℂ) (hχ : χ ∈ D) :
      2*c*η-2*c^2 ≤ 𝔼 x : A, Real.log (‖1+a χ*χ x‖^2) := by
    calc
      _ ≤ 2*c*‖𝔼 x : A, χ x‖-2*c^2 := by
        gcongr
        exact hspec χ hχ
      _ = 𝔼 x : A, (2*c*(u χ*χ x).re-2*c^2) := by
        rw [expect_sub_distrib, ← mul_expect, Fintype.expect_const, hphaseMean]
      _ ≤ _ := expect_le_expect (fun (x : A) _ ↦ hlogterm χ (x : G))
  have hlogP (x : G) : Real.log (P x) = ∑ χ ∈ D, Real.log (‖1+a χ*χ x‖^2) :=
    Real.log_prod (fun χ _ ↦ (hpterm χ x).ne')
  have hloglower : (D.card : ℝ)*(2*c*η-2*c^2) ≤ 𝔼 x : A, Real.log (P x) := by
    simp_rw [hlogP]
    rw [expect_sum_comm]
    calc
      _ = ∑ χ ∈ D, (2*c*η-2*c^2) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hmeanterm
  have hlogupper : (𝔼 x : A, Real.log (P x)) ≤ (D.card : ℝ)*c^2-Real.log (density A) := by
    calc
      _ ≤ Real.log (𝔼 x : A, P x) := expect_log_le_log_expect _ (fun x ↦ hP x)
      _ ≤ Real.log ((1+c^2)^D.card / density A) :=
        Real.log_le_log (expect_pos (fun x _ ↦ hP x) univ_nonempty) hPupper
      _ = (D.card : ℝ)*Real.log (1+c^2)-Real.log (density A) := by
        rw [Real.log_div (pow_pos (by positivity) _).ne' hα.ne', Real.log_pow]
      _ ≤ _ := by
        gcongr
        have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+c^2)
        linarith
  have hcoef : η^2/4 ≤ 2*c*η-3*c^2 := by dsimp [c]; nlinarith [sq_nonneg η]
  have hlog : (D.card : ℝ)*(η^2/4) ≤ Real.log (1/density A) := by
    rw [one_div, Real.log_inv]
    have := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg D.card : (0 : ℝ) ≤ D.card)
    nlinarith [hloglower.trans hlogupper]
  apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
  nlinarith

/-- The whole large spectrum lies in the {−1,0,1}-span of logarithmically many characters. -/
theorem exists_spectrum_generators (A : Finset G) (hA : A.Nonempty)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ spectrum A η ∧
      D.card ≤ ⌊4*Real.log (1/density A)/η^2⌋₊ ∧ spectrum A η ⊆ D.mulSpan := by
  apply exists_subset_mulSpan_card_le_of_forall_mulDissociated
  intro D hD hdis
  apply Nat.le_floor
  exact dissociated_spectrum_bound A hA hη hη1 D hdis
    (fun χ hχ ↦ (mem_filter.mp (hD hχ)).2)

#print axioms dissociated_spectrum_bound
#print axioms exists_spectrum_generators
end Erdos3ChangSpectrum
