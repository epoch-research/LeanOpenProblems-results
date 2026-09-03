import FormalConjecturesUtil

/-! A one-sided quadratic exponential majorant valid for every nonnegative
Laplace parameter. The integral remainder avoids a removable singularity at
zero. These are analytic lemmas only. -/
namespace Erdos970.Resampling
open Real MeasureTheory

noncomputable def expRemainderKernel (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, (1 - u) * exp (u * x)

lemma expRemainderKernel_nonneg (x : ℝ) : 0 ≤ expRemainderKernel x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  exact mul_nonneg (sub_nonneg.mpr hu.2) (exp_pos _).le

lemma expRemainderKernel_mono : Monotone expRemainderKernel := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((show Continuous (fun u : ℝ => (1 - u) * exp (u * x)) by fun_prop).intervalIntegrable 0 1)
    ((show Continuous (fun u : ℝ => (1 - u) * exp (u * y)) by fun_prop).intervalIntegrable 0 1)
  intro u hu
  exact mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hu.1)) (sub_nonneg.mpr hu.2)

lemma expRemainder_identity (x : ℝ) :
    x ^ 2 * expRemainderKernel x = exp x - 1 - x := by
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => (x * (1 - v) + 1) * exp (v * x))
      (x ^ 2 * ((1 - u) * exp (u * x))) u := by
    convert ((((hasDerivAt_const u 1).sub (hasDerivAt_id u)).const_mul x).add_const 1 |>.mul
      (((hasDerivAt_id u).mul_const x).exp)) using 1 <;> dsimp <;> ring
  have hc : Continuous (fun u : ℝ => x ^ 2 * ((1 - u) * exp (u * x))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hh
  change x ^ 2 * expRemainderKernel x = _ at hh
  simp only [sub_self, mul_zero, zero_add, one_mul, sub_zero, mul_one,
    zero_mul, exp_zero] at hh
  linarith only [hh]

noncomputable def bennettFactor (t B : ℝ) : ℝ := t ^ 2 * expRemainderKernel (t * B)

lemma bennettFactor_nonneg (t B : ℝ) : 0 ≤ bennettFactor t B :=
  mul_nonneg (sq_nonneg _) (expRemainderKernel_nonneg _)

lemma bennettFactor_mul_square (t B : ℝ) :
    bennettFactor t B * B ^ 2 = exp (t * B) - 1 - t * B := by
  rw [← expRemainder_identity (t * B)]
  unfold bennettFactor
  ring

lemma bennettFactor_eq (t B : ℝ) (hB : B ≠ 0) :
    bennettFactor t B = (exp (t * B) - 1 - t * B) / B ^ 2 := by
  apply (eq_div_iff (pow_ne_zero _ hB)).mpr
  exact bennettFactor_mul_square t B

/-- Only an upper bound on x is needed; negative increments are unrestricted. -/
theorem exp_le_bennett (t B x : ℝ) (ht : 0 ≤ t) (hx : x ≤ B) :
    exp (t * x) ≤ 1 + t * x + bennettFactor t B * x ^ 2 := by
  have hm := mul_le_mul_of_nonneg_left
    (expRemainderKernel_mono (mul_le_mul_of_nonneg_left hx ht)) (sq_nonneg (t * x))
  rw [expRemainder_identity] at hm
  unfold bennettFactor
  nlinarith only [hm]

/-- The usual dimensionless Bennett rate. -/
noncomputable def bennettRate (x : ℝ) : ℝ := (1 + x) * log (1 + x) - x

lemma bennett_optimized_exponent (B V u : ℝ) (hB : 0 < B) (hV : 0 < V) (hu : 0 ≤ u) :
    -(log (1 + B * u / V) / B) * u +
      bennettFactor (log (1 + B * u / V) / B) B * V =
      -(V / B ^ 2 * bennettRate (B * u / V)) := by
  rw [bennettFactor_eq _ _ hB.ne']
  have harg : 0 < 1 + B * u / V := by positivity
  have ht : log (1 + B * u / V) / B * B = log (1 + B * u / V) :=
    div_mul_cancel₀ _ hB.ne'
  rw [ht, exp_log harg]
  unfold bennettRate
  field_simp
  <;> ring

#print axioms exp_le_bennett
#print axioms bennett_optimized_exponent
end Erdos970.Resampling
