import FormalConjecturesUtil

/-! Conversions between unit-circle chord errors and real approximation by
integers. All angle choices and integer corrections are exact. -/
namespace Erdos3CircleIntegerApproximation
open scoped ComplexConjugate
set_option maxHeartbeats 2000000

noncomputable def unitAngle (v : ℂ) : ℝ := Complex.arg v/(2*Real.pi)
noncomputable def ephase (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)

lemma ephase_norm (t : ℝ) : ‖ephase t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma unit_arg_representation (v : ℂ) (hv : ‖v‖ = 1) :
    Complex.exp (Complex.I*(Complex.arg v : ℂ)) = v := by
  have hh := Complex.norm_mul_exp_arg_mul_I v
  rw [hv,Complex.ofReal_one,one_mul] at hh
  simpa only [mul_comm Complex.I] using hh

lemma ephase_unitAngle (v : ℂ) (hv : ‖v‖ = 1) : ephase (unitAngle v) = v := by
  unfold ephase unitAngle
  rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)]
  simpa only [mul_comm Complex.I] using unit_arg_representation v hv

lemma unitAngle_bound (v : ℂ) (hv : ‖v‖ = 1) : |unitAngle v| ≤ ‖v-1‖/4 := by
  have hhalf : |Complex.arg v/2| ≤ Real.pi/2 := by
    rw [abs_div,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_div_of_nonneg_right (Complex.abs_arg_le_pi v) (by norm_num)
  have hj := Real.mul_abs_le_abs_sin hhalf
  have hm := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have he : Real.pi*(2/Real.pi*|Complex.arg v/2|) = |Complex.arg v| := by
    rw [abs_div,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [he] at hm
  have hn := Complex.norm_exp_I_mul_ofReal_sub_one (Complex.arg v)
  rw [unit_arg_representation v hv,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hn
  unfold unitAngle
  rw [abs_div,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).mpr
  rw [hn]
  nlinarith only [hm]

/-- Every small chord error gives a correspondingly small fractional error. -/
theorem exists_integer_near (t : ℝ) : ∃ b : ℤ, |t-(b : ℝ)| ≤ ‖ephase t-1‖/4 := by
  let v := ephase t
  have hv : ‖v‖ = 1 := ephase_norm t
  have he : Complex.exp ((2*Real.pi*t : ℝ)*Complex.I) =
      Complex.exp ((Complex.arg v : ℂ)*Complex.I) := by
    simpa only [mul_comm Complex.I] using (unit_arg_representation v hv).symm
  obtain ⟨b,hb⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hi := congrArg Complex.im hb
  norm_num [Complex.add_im, Complex.mul_im, Complex.mul_re] at hi
  have ht : t-(b : ℝ) = unitAngle v := by
    unfold unitAngle
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)).mpr
    nlinarith only [hi]
  exact ⟨b,ht ▸ unitAngle_bound v hv⟩

lemma ephase_sub_int (t : ℝ) (b : ℤ) : ephase (t-(b : ℝ)) = ephase t := by
  unfold ephase
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-b,?_⟩
  push_cast
  ring

lemma ephase_near_integer (t : ℝ) (b : ℤ) : ‖ephase t-1‖ ≤ 8*|t-(b : ℝ)| := by
  rw [← ephase_sub_int t b]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(t-(b : ℝ)))
  rw [mul_comm Complex.I] at hh
  change ‖ephase (t-(b : ℝ))-1‖ ≤ ‖2*Real.pi*(t-(b : ℝ))‖ at hh
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at hh
  have hp := mul_le_mul_of_nonneg_right Real.pi_le_four (abs_nonneg (t-(b : ℝ)))
  nlinarith only [hh,hp]

lemma ephase_pow (t : ℝ) (n : ℕ) : (ephase t)^n = ephase ((n : ℝ)*t) := by
  unfold ephase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

#print axioms exists_integer_near
#print axioms ephase_near_integer
end Erdos3CircleIntegerApproximation
