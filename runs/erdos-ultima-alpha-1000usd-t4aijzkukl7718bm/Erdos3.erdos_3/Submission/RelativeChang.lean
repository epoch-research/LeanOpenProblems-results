import Submission.RelativeRiesz
import Submission.BohrTranslation

/-! Relative Chang bounds from approximate dissociation. -/
namespace Erdos3RelativeChang
open Finset Erdos3DissociatedRiesz Erdos3ChangAnalytic Erdos3ChangSpectrum
  Erdos3RelativeRiesz Erdos3CorrelationSifting Erdos3PopularAlmostPeriods
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2500000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma mean_subset_le (A C : Finset G) (hA : A.Nonempty) (hC : C.Nonempty)
    (hAC : A ⊆ C) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ((A.card : ℝ)/C.card)*(𝔼 x : A, f x) ≤ 𝔼 x : C, f x := by
  have hAn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hCn : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hh : (∑ x ∈ A, f x) ≤ ∑ x ∈ C, f x :=
    sum_le_sum_of_subset_of_nonneg hAC (fun x _ _ ↦ hf x)
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_coe, sum_coe_sort]
  field_simp
  nlinarith

/-- The logarithmic cost is relative to C. The approximate-orthogonality
error is explicit, and can be fixed before the rank-cutoff argument. -/
theorem relative_spectrum_bound (A C : Finset G) (hA : A.Nonempty)
    (hC : C.Nonempty) (hAC : A ⊆ C) {η ε : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 ≤ ε)
    (D : Finset (AddChar G ℂ)) (hD : ApproxDissociated C ε D)
    (herr : ε*4^D.card ≤ 1)
    (hspec : ∀ χ ∈ D, η ≤ ‖𝔼 a : A, χ a‖) :
    (D.card : ℝ) ≤ 4*Real.log (2/((A.card : ℝ)/C.card))/η^2 := by
  letI : Nonempty A := hA.to_subtype
  letI : Nonempty C := hC.to_subtype
  let τ : ℝ := (A.card : ℝ)/C.card
  have hτ : 0 < τ := div_pos (by exact_mod_cast hA.card_pos)
    (by exact_mod_cast hC.card_pos)
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
  have hPmean : (𝔼 x : C, P x) ≤ 2*(1+c^2)^D.card := by
    have hh := relative_riesz_l2 C hC D hε hD a
    simp only [norm_prod, ← prod_pow, han, prod_const] at hh
    change (𝔼 x : C, P x) ≤ (1+c^2)^D.card+ε*((1+c)^D.card)^2 at hh
    have hb : ((1+c)^D.card)^2 ≤ (4 : ℝ)^D.card := by
      rw [← pow_mul, mul_comm D.card 2, pow_mul]
      apply pow_le_pow_left₀ (sq_nonneg _)
      nlinarith [sq_nonneg c]
    have he : ε*((1+c)^D.card)^2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hb hε).trans herr
    have hone : (1 : ℝ) ≤ (1+c^2)^D.card := one_le_pow₀ (by nlinarith [sq_nonneg c])
    linarith
  have hPweighted : τ*(𝔼 x : A, P x) ≤ 2*(1+c^2)^D.card :=
    (mean_subset_le A C hA hC hAC P (fun x ↦ (hP x).le)).trans hPmean
  have hPupper : (𝔼 x : A, P x) ≤ 2*(1+c^2)^D.card / τ := by
    apply (le_div_iff₀ hτ).mpr
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
  have hlogupper : (𝔼 x : A, Real.log (P x)) ≤
      (D.card : ℝ)*c^2+Real.log (2/τ) := by
    calc
      _ ≤ Real.log (𝔼 x : A, P x) := expect_log_le_log_expect _ (fun x ↦ hP x)
      _ ≤ Real.log (2*(1+c^2)^D.card / τ) :=
        Real.log_le_log (expect_pos (fun x _ ↦ hP x) univ_nonempty) hPupper
      _ = (D.card : ℝ)*Real.log (1+c^2)+Real.log (2/τ) := by
        rw [Real.log_div (by positivity) hτ.ne', Real.log_mul (by norm_num)
          (pow_pos (by positivity) _).ne', Real.log_pow, Real.log_div (by norm_num) hτ.ne']
        ring
      _ ≤ _ := by
        gcongr
        have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+c^2)
        linarith
  have hcoef : η^2/4 ≤ 2*c*η-3*c^2 := by dsimp [c]; nlinarith [sq_nonneg η]
  have hlog : (D.card : ℝ)*(η^2/4) ≤ Real.log (2/τ) := by
    have := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg D.card : (0 : ℝ) ≤ D.card)
    nlinarith [hloglower.trans hlogupper]
  apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
  change (D.card : ℝ)*η^2 ≤ 4*Real.log (2/τ)
  nlinarith

#print axioms relative_spectrum_bound
end Erdos3RelativeChang
