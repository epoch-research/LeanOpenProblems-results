import Submission.U3ApproximateSymmetry

/-! Mixed correlation, localized averaging, and Fourier energy estimates for
the local quadratic correlation step. -/
namespace Erdos3MixedCorrelationFourier
open Finset Erdos3FiniteFourier Erdos3SpectralGraphEnergy
  Erdos3CorrelationSifting Erdos3PopularAlmostPeriods
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def mixedCorr (a b : G → ℂ) (h : G) : ℂ :=
  𝔼 x, a (x+h)*conj (b x)

lemma hat_mixedCorr (a b : G → ℂ) (χ : AddChar G ℂ) :
    hat (mixedCorr a b) χ = hat a χ*conj (hat b χ) := by
  have hinner (x : G) : (𝔼 h, a (x+h)*conj (χ h)) = χ x*hat a χ := by
    simpa only [hat,add_comm x] using hat_shift a x χ
  unfold hat mixedCorr
  simp_rw [expect_mul]
  rw [expect_comm]
  calc
    _ = 𝔼 x, conj (b x)*(𝔼 h, a (x+h)*conj (χ h)) := by
      apply expect_congr rfl
      intro x _
      rw [mul_expect]
      apply expect_congr rfl
      intro h _
      ring
    _ = 𝔼 x, conj (b x)*(χ x*hat a χ) := by simp_rw [hinner]
    _ = (𝔼 x, conj (b x)*χ x)*hat a χ := by simp only [← mul_assoc,← expect_mul]
    _ = _ := by
      rw [← expect_mul]
      change (𝔼 x, conj (b x)*χ x)*hat a χ = hat a χ*conj (hat b χ)
      rw [mul_comm]
      congr 1
      rw [hat,expect_conj]
      apply expect_congr rfl
      intro x _
      simp only [map_mul,starRingEnd_self_apply]

lemma mixedCorr_energy (a b : G → ℂ) :
    (𝔼 h, ‖mixedCorr a b h‖^2) = ∑ χ : AddChar G ℂ, ‖hat a χ‖^2*‖hat b χ‖^2 := by
  rw [← parseval]
  simp only [hat_mixedCorr,norm_mul,Complex.norm_conj,mul_pow]

/-- A single Fourier coefficient of the first function accounts for the
mixed correlation energy, relative to the L2 mass of the second function. -/
theorem exists_coefficient_from_mixed_energy (a b : G → ℂ) :
    ∃ χ : AddChar G ℂ, (𝔼 h, ‖mixedCorr a b h‖^2) ≤
      ‖hat a χ‖^2*(𝔼 x, ‖b x‖^2) := by
  obtain ⟨χ,_,hχ⟩ := exists_max_image univ (fun χ : AddChar G ℂ ↦ ‖hat a χ‖^2) univ_nonempty
  refine ⟨χ,?_⟩
  rw [mixedCorr_energy,← parseval,mul_sum]
  exact sum_le_sum (fun ψ hψ ↦ mul_le_mul_of_nonneg_right (hχ ψ hψ) (sq_nonneg _))

lemma complex_masked_expect (Q : Finset G) (hQ : Q.Nonempty) (f : G → ℂ) :
    (𝔼 x, if x ∈ Q then f x else 0) = (density Q : ℂ)*(𝔼 x : Q, f x) := by
  have hQ0 : (Q.card : ℂ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  simp only [density,Fintype.expect_eq_sum_div_card,Fintype.card_coe,
    Complex.ofReal_div,Complex.ofReal_natCast]
  rw [sum_coe_sort Q f]
  simp only [sum_ite_mem,univ_inter]
  field_simp

lemma density_mul_subset_expect_le (Q : Finset G) (hQ : Q.Nonempty)
    (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) : density Q*(𝔼 x : Q, g x) ≤ 𝔼 x, g x := by
  rw [← expect_indicator_mul Q hQ]
  apply expect_le_expect
  intro x _
  by_cases hx : x ∈ Q
  · simp only [indicator,if_pos hx,one_mul,le_refl]
  · simpa only [indicator,if_neg hx,zero_mul] using hg x

lemma mixedCorr_mask (Q : Finset G) (hQ : Q.Nonempty) (a b : G → ℂ) (h : G) :
    mixedCorr a (fun x ↦ if x ∈ Q then b x else 0) h =
      (density Q : ℂ)*(𝔼 x : Q, a ((x : G)+h)*conj (b x)) := by
  unfold mixedCorr
  rw [← complex_masked_expect Q hQ (fun x ↦ a (x+h)*conj (b x))]
  apply expect_congr rfl
  intro x _
  by_cases hx : x ∈ Q <;> simp [hx]

/-- If normalized local correlations are large on H, the first function
has a Fourier coefficient with squared norm at least kappa*density(H)*density(Q).
This retains the support-density factors required for a local inverse bound. -/
theorem localized_mixed_inverse (H Q : Finset G) (hH : H.Nonempty) (hQ : Q.Nonempty)
    (a b : G → ℂ) (hb : ∀ x, ‖b x‖ ≤ 1) {κ : ℝ}
    (hmean : κ ≤ 𝔼 h : H, ‖𝔼 x : Q, a ((x : G)+h)*conj (b x)‖^2) :
    ∃ χ : AddChar G ℂ, κ*density H*density Q ≤ ‖hat a χ‖^2 := by
  let bQ : G → ℂ := fun x ↦ if x ∈ Q then b x else 0
  have hσQ : 0 < density Q := density_pos Q hQ
  have hσH : 0 < density H := density_pos H hH
  have he (h : G) : ‖mixedCorr a bQ h‖^2 =
      (density Q)^2*‖𝔼 x : Q, a ((x : G)+h)*conj (b x)‖^2 := by
    rw [mixedCorr_mask Q hQ a b h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσQ,mul_pow]
  have hmass : (𝔼 x, ‖bQ x‖^2) ≤ density Q := by
    apply Erdos3AveragedAntisymmetry.support_mass_le Q bQ
    · intro x
      dsimp [bQ]
      split_ifs
      · exact hb x
      · norm_num
    · intro x hx
      exact if_neg hx
  have hl : κ*density H*(density Q)^2 ≤ 𝔼 h, ‖mixedCorr a bQ h‖^2 := by
    have hh := density_mul_subset_expect_le H hH (fun h ↦ ‖mixedCorr a bQ h‖^2) (fun _ ↦ sq_nonneg _)
    simp_rw [he] at hh
    rw [← mul_expect] at hh
    have hm := mul_le_mul_of_nonneg_left hmean (mul_nonneg hσH.le (sq_nonneg (density Q)))
    simp_rw [he]
    nlinarith only [hm,hh]
  obtain ⟨χ,hχ⟩ := exists_coefficient_from_mixed_energy a bQ
  have hh := hl.trans (hχ.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)))
  refine ⟨χ,(mul_le_mul_iff_left₀ hσQ).mp ?_⟩
  convert hh using 1 <;> ring

#print axioms localized_mixed_inverse
end Erdos3MixedCorrelationFourier
