import Submission.RemainderGcdProfile

/-! Mobius inversion of finite gcd-pattern functions, including coefficient
and Lipschitz costs. These costs are retained in weighted row applications. -/
namespace Erdos972GcdProfileExpansion

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable def profileFunction (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

@[simp] lemma profileFunction_apply (f : ℕ → ℝ) (n : ℕ) :
    profileFunction f n = if n = 0 then 0 else f n := rfl

noncomputable def profileCoeff (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  (profileFunction f * (μ : ArithmeticFunction ℝ)) d

lemma profileCoeff_eq_sum (f : ℕ → ℝ) (d : ℕ) :
    profileCoeff f d = ∑ e ∈ d.divisors, f e * (μ (d/e) : ℝ) := by
  rw [profileCoeff, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun e k => profileFunction f e * (μ : ArithmeticFunction ℝ) k)]
  apply sum_congr rfl
  intro e he
  simp only [profileFunction_apply, ArithmeticFunction.intCoe_apply,
    if_neg (Nat.pos_of_mem_divisors he).ne']

lemma sum_profileCoeff (f : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, profileCoeff f d) = f n := by
  have he : (profileFunction f * (μ : ArithmeticFunction ℝ))*ζ = profileFunction f := by
    rw [mul_assoc, coe_moebius_mul_coe_zeta, mul_one]
  have hh := congrArg (fun a : ArithmeticFunction ℝ => a n) he
  simpa only [coe_mul_zeta_apply, profileCoeff, profileFunction_apply, if_neg hn] using hh

lemma divisors_filter_dvd {F n : ℕ} (hF : F ≠ 0) :
    F.divisors.filter (fun d => d ∣ n) = (n.gcd F).divisors := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  have hg : n.gcd F ≠ 0 := (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hF)).ne'
  tauto

/-- A gcd-pattern function is a signed divisor polynomial with divisors of F. -/
theorem gcd_profile_expansion (f : ℕ → ℝ) {F : ℕ} (hF : F ≠ 0) (n : ℕ) :
    f (n.gcd F) = ∑ d ∈ F.divisors, if d ∣ n then profileCoeff f d else 0 := by
  rw [← sum_filter, divisors_filter_dvd hF, sum_profileCoeff]
  exact (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hF)).ne'

lemma profileCoeff_sub (f g : ℕ → ℝ) (d : ℕ) :
    profileCoeff (fun r => f r-g r) d = profileCoeff f d-profileCoeff g d := by
  simp only [profileCoeff_eq_sum, sub_mul, sum_sub_distrib]

lemma profileCoeff_bound {F d : ℕ} (hF : F ≠ 0) (hd : d ∣ F) (f : ℕ → ℝ) {H : ℝ}
    (hf : ∀ r ∈ F.divisors, |f r| ≤ H) :
    |profileCoeff f d| ≤ d.divisors.card * H := by
  rw [profileCoeff_eq_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e ∈ d.divisors, H := by
      apply sum_le_sum
      intro e he
      have hef : e ∈ F.divisors := Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors he).trans hd, hF⟩
      have hmu : |(μ (d/e) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d/e)
      rw [abs_mul]
      exact (mul_le_mul (hf e hef) hmu (abs_nonneg _) ((abs_nonneg _).trans (hf e hef))).trans_eq (mul_one H)
    _ = _ := by simp

noncomputable def profileCost (F : ℕ) : ℝ := ∑ d ∈ F.divisors, (d.divisors.card : ℝ)

lemma profileCost_nonneg (F : ℕ) : 0 ≤ profileCost F := sum_nonneg (fun _ _ => Nat.cast_nonneg _)

noncomputable def meanProfile (F : ℕ) (Φ : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 F, Φ (n.gcd F) x)/F

/-- The signed divisor density equals an ordinary finite average. -/
theorem profile_density_eq_mean (f : ℕ → ℝ) {F : ℕ} (hF : F ≠ 0) :
    (∑ d ∈ F.divisors, profileCoeff f d/d) =
      (∑ n ∈ Ioc 0 F, f (n.gcd F))/F := by
  have hFR : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF
  have he : (∑ n ∈ Ioc 0 F, f (n.gcd F)) =
      (F : ℝ) * ∑ d ∈ F.divisors, profileCoeff f d/d := by
    simp_rw [gcd_profile_expansion f hF]
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro d hd
    have hdF := Nat.dvd_of_mem_divisors hd
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
    rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, Nat.cast_div hdF hdR]
    ring
  rw [he, mul_div_cancel_left₀ _ hFR]

/-- The main-term average retains the original Lipschitz constant; there
is no loss of a factor equal to the number of gcd patterns here. -/
theorem meanProfile_lipschitz {F : ℕ} (hF : F ≠ 0) (Φ : ℕ → ℝ → ℝ) {L : ℝ}
    (hΦ : ∀ r ∈ F.divisors, ∀ x y, |Φ r x-Φ r y| ≤ L*|x-y|) (x y : ℝ) :
    |meanProfile F Φ x-meanProfile F Φ y| ≤ L*|x-y| := by
  have hFR : (0 : ℝ) < F := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
  rw [meanProfile, meanProfile, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hFR]
  apply (div_le_iff₀ hFR).mpr
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 F, L*|x-y| := by
      apply sum_le_sum
      intro n hn
      exact hΦ _ (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n F,
        hF⟩) x y
    _ = _ := by simp; ring

#print axioms gcd_profile_expansion
#print axioms profile_density_eq_mean
#print axioms meanProfile_lipschitz

end Erdos972GcdProfileExpansion
