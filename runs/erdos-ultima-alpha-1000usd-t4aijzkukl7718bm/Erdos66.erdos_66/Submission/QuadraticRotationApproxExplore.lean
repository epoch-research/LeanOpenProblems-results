import FormalConjecturesUtil

/-! Rational approximants to sqrt(2) with denominators comparable to a
prescribed horizon. These will supply short rotation blocks. -/
namespace Erdos66QuadraticRotationApprox
open scoped Classical
set_option maxHeartbeats 1600000

lemma sqrt_two_rat_lower (r : ℚ) (hr : |Real.sqrt 2-(r : ℝ)| ≤ 1) :
    1 ≤ 5*(r.den : ℝ)^2*|Real.sqrt 2-(r : ℝ)| := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsn := Real.sqrt_nonneg (2 : ℝ)
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hs2 : Real.sqrt 2 < (2 : ℝ) := by nlinarith
  have hrb := abs_le.mp hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hr3 : (r : ℝ) < 3 := by linarith
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hne : (2*(r.den : ℤ)^2-r.num^2 : ℤ) ≠ 0 := by
    intro h
    have hcast : (2 : ℝ)*(r.den : ℝ)^2-(r.num : ℝ)^2=0 := by exact_mod_cast h
    have he : (r : ℝ)^2=2 := by
      rw [Rat.cast_def,div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hd.ne')).mpr
      nlinarith
    have her : Real.sqrt 2=(r : ℝ) := by nlinarith
    exact irrational_sqrt_two.ne_rat r her
  have hi : (1 : ℝ) ≤ |2*(r.den : ℝ)^2-(r.num : ℝ)^2| := by
    exact_mod_cast Int.one_le_abs hne
  have hprod : (Real.sqrt 2-(r : ℝ))*(Real.sqrt 2+(r : ℝ))*(r.den : ℝ)^2 =
      2*(r.den : ℝ)^2-(r.num : ℝ)^2 := by
    rw [show (Real.sqrt 2-(r : ℝ))*(Real.sqrt 2+(r : ℝ))=2-(r : ℝ)^2 by nlinarith,
      Rat.cast_def]
    field_simp
  have habs := congrArg abs hprod
  simp only [abs_mul,abs_pow,abs_of_pos hd,
    abs_of_pos (show 0 < Real.sqrt 2+(r : ℝ) by positivity)] at habs
  rw [← habs] at hi
  have hh := mul_le_mul_of_nonneg_right
    (show Real.sqrt 2+(r : ℝ) ≤ 5 by linarith)
    (show 0 ≤ |Real.sqrt 2-(r : ℝ)| *(r.den : ℝ)^2 by positivity)
  nlinarith only [hi,hh]

/-- Every positive horizon N has a reduced rational approximant whose
block length lies between (N+1)/5 and N. -/
theorem exists_comparable_approx (N : ℕ) (hN : 0 < N) :
    ∃ r : ℚ, r.den ≤ N ∧ N+1 ≤ 5*r.den ∧
      |Real.sqrt 2-(r : ℝ)| ≤ 1/(((N : ℝ)+1)*r.den) ∧
      (r.den : ℝ)^2*|Real.sqrt 2-(r : ℝ)| ≤ 1 := by
  obtain ⟨r,hr,hdN⟩ := Real.exists_rat_abs_sub_le_and_den_le (Real.sqrt 2) hN
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hd1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hdN' : (r.den : ℝ) ≤ N := by exact_mod_cast hdN
  have hprod : (0 : ℝ) < ((N : ℝ)+1)*r.den := by positivity
  have hr1 : |Real.sqrt 2-(r : ℝ)| ≤ 1 := by
    apply hr.trans
    apply (div_le_one hprod).mpr
    nlinarith
  have hlo := sqrt_two_rat_lower r hr1
  have hup := (le_div_iff₀ hprod).mp hr
  have hlength : (N : ℝ)+1 ≤ 5*r.den := by
    have h1 := mul_le_mul_of_nonneg_right hlo (show 0 ≤ (N : ℝ)+1 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hup (show 0 ≤ 5*(r.den : ℝ) by positivity)
    nlinarith only [h1,h2,hd]
  refine ⟨r,hdN,by exact_mod_cast hlength,hr,?_⟩
  have habs := abs_nonneg (Real.sqrt 2-(r : ℝ))
  have hmul := mul_le_mul_of_nonneg_right (show (r.den : ℝ) ≤ (N : ℝ)+1 by linarith)
    (show 0 ≤ (r.den : ℝ)*|Real.sqrt 2-(r : ℝ)| by positivity)
  nlinarith only [hup,hmul]

end Erdos66QuadraticRotationApprox
