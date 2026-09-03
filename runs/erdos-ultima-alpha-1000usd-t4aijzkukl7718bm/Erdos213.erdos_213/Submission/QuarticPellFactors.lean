import Submission.PolynomialPellClassification

/-! Auxiliary real-algebra restrictions on the quadratic square roots of the
quartic Pell motions. These do not classify all compatible point sets. -/
namespace Erdos213.QuarticPellFactors
noncomputable section
set_option maxHeartbeats 1000000

/-- The positive half-angle parameter covers every slope in the complete
quartic template; this avoids assuming a rational or numerical slope. -/
lemma positive_half_angle (a s : ℝ) (hs : 0<s) (hn : a^2+s^2=1) :
    ∃ k : ℝ, 0<k ∧ a=(1-k^2)/(1+k^2) ∧ s=2*k/(1+k^2) := by
  have ha : a^2<1 := by nlinarith [sq_pos_of_pos hs]
  have hd : 0<1+a := by nlinarith [sq_nonneg (a+1)]
  let k := s/(1+a)
  have hk : 0<k := div_pos hs hd
  have hkd : 1+k^2=2/(1+a) := by
    dsimp [k]
    field_simp
    nlinarith [hn]
  refine ⟨k,hk,?_,?_⟩
  · rw [hkd]
    dsimp [k]
    field_simp
    nlinarith [hn]
  · rw [hkd]
    dsimp [k]
    field_simp

/-- The real part (multiplied by nine) of the essential discriminant factor. -/
def discReal (k h r : ℝ) : ℝ :=
  9*k^2*h^2*r-16*k^2*r^2-16*k*h*r^2-9*k^2*r-36*k*h*r-
    9*h^2*r-16*k*h-16*h^2+9*r

/-- The imaginary part, up to a nonzero constant. -/
def discImag (k h r : ℝ) : ℝ :=
  (k*h-1)*(8*k*r^2+7*k*r+7*h*r+8*h)

lemma essential_discriminant_relation (k h r : ℝ) (hr : r≠0)
    (ha : discReal k h r=0) (hb : discImag k h r=0) : k*h=1 := by
  by_contra hh
  have hb' : 8*k*r^2+7*k*r+7*h*r+8*h=0 :=
    (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hh)
  have hf : r*(9*k^2*h^2+5*k^2-8*k*h+5*h^2+9)=0 := by
    dsimp [discReal] at ha
    linear_combination ha+2*(k+h)*hb'
  have hp : 0<9*k^2*h^2+5*k^2-8*k*h+5*h^2+9 := by
    nlinarith [sq_nonneg (k*h),sq_nonneg (k-h),sq_nonneg k,sq_nonneg h]
  exact (mul_ne_zero hr (ne_of_gt hp)) hf

lemma essential_discriminant_negative_root_scale (k h r : ℝ) (hr : r≠0)
    (ha : discReal k h r=0) (hb : discImag k h r=0) : r<0 := by
  have hh := essential_discriminant_relation k h r hr ha hb
  have he : 9*(k^2+h^2+2)*r+16*(k^2+1)*r^2+16*(1+h^2)=0 := by
    dsimp [discReal] at ha
    linear_combination -ha + (9*r*(k*h-3)-16*r^2-16)*hh
  by_contra hn
  have hr' : 0≤r := le_of_not_gt hn
  have hp : 0<9*(k^2+h^2+2)*r+16*(k^2+1)*r^2+16*(1+h^2) := by
    positivity
  linarith

/-- The real and imaginary equations of a normalized quartic square root
force every zero into the upper half-plane. No unit-circle equation is needed. -/
lemma quadratic_root_im_pos (a s x y : ℝ) (hs : 0<s)
    (hre : x^2-y^2-3*a*x+s*y-2*s^2=0)
    (him : 2*x*y-s*x-3*a*y+2*a*s=0) : 0<y := by
  by_contra hn
  have hy : y≤0 := le_of_not_gt hn
  have hd : 0≤y^2-s*y := by
    nlinarith [sq_nonneg y,mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) hy]
  have he : a^2*(9*(y^2-s*y)+2*s^2)+
      (y^2-s*y+2*s^2)*(4*(y^2-s*y)+s^2)=0 := by
    linear_combination -(2*y-s)^2*hre +
      ((2*y-s)*x+a*(3*y-2*s)-3*a*(2*y-s))*him
  have hp : 0<a^2*(9*(y^2-s*y)+2*s^2)+
      (y^2-s*y+2*s^2)*(4*(y^2-s*y)+s^2) := by
    positivity
  linarith

/-- A complex form of `quadratic_root_im_pos`. -/
lemma stable_quadratic (a s : ℝ) (hs : 0<s) (z : ℂ)
    (hz : z^2-((3*a : ℝ)+Complex.I*s)*z+
      2*Complex.I*s*((a : ℂ)+Complex.I*s)=0) : 0<z.im := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.zero_re,Complex.add_im,Complex.sub_im,Complex.zero_im,
    Complex.re_ofNat,Complex.im_ofNat,pow_two] at hr hi
  apply quadratic_root_im_pos a s z.re z.im hs
  · nlinarith [hr]
  · nlinarith [hi]

/-- An upper-stable quadratic and a conjugate upper-stable quadratic cannot
have a common zero. This is a shared-root restriction, not a square-norm test. -/
lemma stable_quadratic_no_conjugate_common_root
    (a s b u : ℝ) (hs : 0<s) (hu : 0<u) (z : ℂ)
    (hz : z^2-((3*a : ℝ)+Complex.I*s)*z+
      2*Complex.I*s*((a : ℂ)+Complex.I*s)=0)
    (hw : (starRingEnd ℂ z)^2-((3*b : ℝ)+Complex.I*u)*(starRingEnd ℂ z)+
      2*Complex.I*u*((b : ℂ)+Complex.I*u)=0) : False := by
  have hp := stable_quadratic a s hs z hz
  have hn := stable_quadratic b u hu (starRingEnd ℂ z) hw
  simp only [Complex.conj_im] at hn
  linarith

/-- The nontrivial direction factor in the reflected-edge resultant is
nonzero on the product of two unit circles, by a strict norm bound. -/
lemma reflected_direction_factor_ne_zero (u v : ℂ)
    (hu : ‖u‖=1) (hv : ‖v‖=1) :
    128*u^8+11827*u^6*v^2+299523*u^4*v^4+11827*u^2*v^6+128*v^8≠0 := by
  intro he
  have hc : 299523*u^4*v^4= -(128*u^8+11827*u^6*v^2+11827*u^2*v^6+128*v^8) := by
    linear_combination he
  have hb : ‖128*u^8+11827*u^6*v^2+11827*u^2*v^6+128*v^8‖≤23910 := by
    calc
      _ ≤ ‖128*u^8+11827*u^6*v^2+11827*u^2*v^6‖+‖128*v^8‖ := norm_add_le _ _
      _ ≤ (‖128*u^8+11827*u^6*v^2‖+‖11827*u^2*v^6‖)+‖128*v^8‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖128*u^8‖+‖11827*u^6*v^2‖)+‖11827*u^2*v^6‖)+‖128*v^8‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ = 23910 := by norm_num [norm_mul,norm_pow,hu,hv]
  have hn := congrArg norm hc
  rw [norm_neg] at hn
  norm_num [norm_mul,norm_pow,hu,hv] at hn
  linarith

/-- After the unit-direction elimination, the surviving reciprocal quartic
in the positive scale has an explicit positive decomposition. -/
lemma reflected_scale_factor_pos (z m : ℝ) (hz : z ≤ 2) (hm : 0 < m) :
    0<16*(z-2)^2*(m^4+1)+(-64*z^2+49*z+158)*(m^3+m)+
      (96*z^2+30*z-336)*m^2 := by
  have hh : 0 ≤ 2-z := by linarith
  have he : 16*(z-2)^2*(m^4+1)+(-64*z^2+49*z+158)*(m^3+m)+
      (96*z^2+30*z-336)*m^2 =
      16*(z-2)^2*(m-1)^4+207*(2-z)*m*(m-1)^2+108*m^2 := by ring
  rw [he]
  positivity

/-- The real positive scale forced by the radial elimination is one,
using only the unit norm of the complex product parameter. -/
lemma positive_scale_of_unit_alternative (m : ℝ) (hm : 0 < m)
    (w : ℂ) (hw : ‖w‖=1)
    (he : ((m : ℂ)^2-1)*((m : ℂ)^3-w)=0) : m=1 := by
  rcases mul_eq_zero.mp he with h | h
  · have hh : m^2=1 := by exact_mod_cast (sub_eq_zero.mp h)
    have hf : (m-1)*(m+1)=0 := by nlinarith [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt (by positivity)))
  · have hn := congrArg norm (sub_eq_zero.mp h)
    have hh : m^3=1 := by
      simpa [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm,hw] using hn
    have hf : (m-1)*(m^2+m+1)=0 := by nlinarith [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt (by positivity)))

#print axioms positive_scale_of_unit_alternative
#print axioms reflected_direction_factor_ne_zero
#print axioms reflected_scale_factor_pos
#print axioms positive_half_angle
#print axioms essential_discriminant_relation
#print axioms essential_discriminant_negative_root_scale
#print axioms stable_quadratic
#print axioms stable_quadratic_no_conjugate_common_root
end
end Erdos213.QuarticPellFactors
