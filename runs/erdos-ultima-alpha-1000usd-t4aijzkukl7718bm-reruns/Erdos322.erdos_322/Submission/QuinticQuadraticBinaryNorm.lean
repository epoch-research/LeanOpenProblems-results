import FormalConjecturesUtil

/-! Rigidity of a repeated-pair binary quadratic quintic norm identity.
This concerns a particular construction, not unrestricted representation counts. -/
namespace Erdos322Research.QuinticQuadraticBinaryNorm

noncomputable section
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

private theorem hankel_discriminant (t b s : ℝ)
    (h0 : t*(t+4-4*b^2-12*b*s-2*s^2)-(t+4-4*b-8*s)*(t+4-4*b-8*s)=0)
    (h1 : t*(t+4-4*b^3-12*b^2*s-2*b*s^2)-(t+4-4*b-8*s)*(t+4-4*b^2-12*b*s-2*s^2)=0)
    (h2 : t*(t+4-4*b^4-8*b^3*s)-(t+4-4*b-8*s)*(t+4-4*b^3-12*b^2*s-2*b*s^2)=0)
    (h3 : t*(t+4-4*b^5)-(t+4-4*b-8*s)*(t+4-4*b^4-8*b^3*s)=0)
    (h4 : (t+4-4*b-8*s)*(t+4-4*b^3-12*b^2*s-2*b*s^2)-(t+4-4*b^2-12*b*s-2*s^2)*(t+4-4*b^2-12*b*s-2*s^2)=0)
    (h5 : (t+4-4*b-8*s)*(t+4-4*b^4-8*b^3*s)-(t+4-4*b^2-12*b*s-2*s^2)*(t+4-4*b^3-12*b^2*s-2*b*s^2)=0)
    (h6 : (t+4-4*b-8*s)*(t+4-4*b^5)-(t+4-4*b^2-12*b*s-2*s^2)*(t+4-4*b^4-8*b^3*s)=0)
    (h7 : (t+4-4*b^2-12*b*s-2*s^2)*(t+4-4*b^4-8*b^3*s)-(t+4-4*b^3-12*b^2*s-2*b*s^2)*(t+4-4*b^3-12*b^2*s-2*b*s^2)=0)
    : s^3*(3*s^2-16*s+192)=0 := by
  linear_combination
    (42907/96*b*s ^ 3 + 3805/48*s ^ 4 - 59/64*t*b*s - 3805/96*t*s ^ 2 + 41/16*b*s ^ 2 + 1/16*s ^ 3 - 185/96*t*b + 731/48*t*s - 5179/48*b*s - 8483/48*s ^ 2 + 19/6*t - 19/8*b + 233/4*s + 38/3) * h0 +
    (59/64*t*b*s - 59/16*b ^ 2*s + 3805/96*t*s ^ 2 + 59/16*b*s ^ 2 - 4585/16*s ^ 3 + 185/96*t*b - 185/24*b ^ 2 - 731/48*t*s - 169/24*b*s + 2343/16*s ^ 2 - 19/6*t + 221/6*b + 155/6*s - 46/3) * h1 +
    (-91/6*s + 241/24) * h2 +
    (-59/8) * h3 +
    (-59/64*t*b*s + 59/16*b ^ 2*s - 3805/96*t*s ^ 2 - 185/96*t*b + 539/24*b ^ 2 + 731/48*t*s + 571/48*b*s - 1465/12*s ^ 2 + 19/6*t - 683/8*b + 2585/24*s - 1817/24) * h4 +
    (-905/48*s + 1471/24) * h5 +
    (-59/8) * h6 +
    (-59/16*s - 1/3) * h7

/-- Necessary coefficient relations force the mixed square coefficient to vanish. -/
theorem coefficient_rigidity (b e f s : ℝ)
    (h1 : 4*b+8*s+e^4*f=4+e^5)
    (h2 : 4*b^2+12*b*s+2*s^2+e^3*f^2=4+e^5)
    (h3 : 4*b^3+12*b^2*s+2*b*s^2+e^2*f^3=4+e^5)
    (h4 : 4*b^4+8*b^3*s+e*f^4=4+e^5)
    (h5 : 4*b^5+f^5=4+e^5) : s=0 := by
  have q1 : e^5+4-4*b-8*s=e^4*f := by linarith only [h1]
  have q2 : e^5+4-4*b^2-12*b*s-2*s^2=e^3*f^2 := by linarith only [h2]
  have q3 : e^5+4-4*b^3-12*b^2*s-2*b*s^2=e^2*f^3 := by linarith only [h3]
  have q4 : e^5+4-4*b^4-8*b^3*s=e*f^4 := by linarith only [h4]
  have q5 : e^5+4-4*b^5=f^5 := by linarith only [h5]
  have hz : s^3*(3*s^2-16*s+192)=0 := by
    apply hankel_discriminant (e^5) b s <;>
      simp only [q1,q2,q3,q4,q5] <;> ring
  have hp : 0 < 3*s^2-16*s+192 := by nlinarith [sq_nonneg (3*s-8)]
  exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_right hp.ne')

private def core (b e f s : ℝ) : ℝ[X] :=
  4*(1+C b*X)^5 + 40*(1+C b*X)^3*C s*X +
  20*(1+C b*X)*(C s)^2*X^2 + (C e+C f*X)^5 -
  C (4+e^5)*(1+X)^5

private theorem core_expansion (b e f s : ℝ) : core b e f s =
    C (5*(4*b+8*s+e^4*f-4-e^5))*X +
    C (10*(4*b^2+12*b*s+2*s^2+e^3*f^2-4-e^5))*X^2 +
    C (10*(4*b^3+12*b^2*s+2*b*s^2+e^2*f^3-4-e^5))*X^3 +
    C (5*(4*b^4+8*b^3*s+e*f^4-4-e^5))*X^4 +
    C (4*b^5+f^5-4-e^5)*X^5 := by
  simp only [core,map_add,map_sub,map_mul,map_pow,map_ofNat]
  ring

private theorem core_zero_coefficients (b e f s : ℝ) (h : core b e f s=0) :
    (4*b+8*s+e^4*f=4+e^5) ∧
    (4*b^2+12*b*s+2*s^2+e^3*f^2=4+e^5) ∧
    (4*b^3+12*b^2*s+2*b*s^2+e^2*f^3=4+e^5) ∧
    (4*b^4+8*b^3*s+e*f^4=4+e^5) ∧
    (4*b^5+f^5=4+e^5) := by
  rw [core_expansion] at h
  have h1 := congrArg (fun p : ℝ[X] ↦ p.coeff 1) h
  have h2 := congrArg (fun p : ℝ[X] ↦ p.coeff 2) h
  have h3 := congrArg (fun p : ℝ[X] ↦ p.coeff 3) h
  have h4 := congrArg (fun p : ℝ[X] ↦ p.coeff 4) h
  have h5 := congrArg (fun p : ℝ[X] ↦ p.coeff 5) h
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_zero] at h1 h2 h3 h4 h5
  norm_num at h1 h2 h3 h4 h5
  exact ⟨by linarith only [h1],by linarith only [h2],by linarith only [h3],
    by linarith only [h4],by linarith only [h5]⟩

private theorem normalized_core_zero (b e f B : ℝ)
    (h : ∀ x y : ℝ,
      2*(x^2+b*y^2+B*x*y)^5 + 2*(x^2+b*y^2-B*x*y)^5 +
      (e*x^2+f*y^2)^5 = (4+e^5)*(x^2+y^2)^5) : core b e f (B^2)=0 := by
  have he (t : ℝ) : (core b e f (B^2)).eval (t^2)=0 := by
    calc
      _ = 2*(1+b*t^2+B*t)^5 + 2*(1+b*t^2-B*t)^5 +
          (e+f*t^2)^5 - (4+e^5)*(1+t^2)^5 := by
        simp only [core,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_ofNat,
          eval_one]
        ring
      _ = 0 := by
        have hh := h 1 t
        norm_num at hh
        linarith only [hh]
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro u hu
  change (core b e f (B^2)).eval u = (0 : ℝ[X]).eval u
  simpa only [Real.sq_sqrt hu,eval_zero] using he (Real.sqrt u)

/-- In the normalized binary chart, any real mixed coefficient must be zero. -/
theorem normalized_mixed_zero (b e f B : ℝ)
    (h : ∀ x y : ℝ,
      2*(x^2+b*y^2+B*x*y)^5 + 2*(x^2+b*y^2-B*x*y)^5 +
      (e*x^2+f*y^2)^5 = (4+e^5)*(x^2+y^2)^5) : B=0 := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := core_zero_coefficients b e f (B^2)
    (normalized_core_zero b e f B h)
  exact sq_eq_zero_iff.mp (coefficient_rigidity b e f (B^2) h1 h2 h3 h4 h5)

/-- With nonzero target, the normalized chart is radial. -/
theorem normalized_radial (b e f B : ℝ) (hN : 4+e^5 ≠ 0)
    (h : ∀ x y : ℝ,
      2*(x^2+b*y^2+B*x*y)^5 + 2*(x^2+b*y^2-B*x*y)^5 +
      (e*x^2+f*y^2)^5 = (4+e^5)*(x^2+y^2)^5) : b=1 ∧ e=f ∧ B=0 := by
  have hB := normalized_mixed_zero b e f B h
  subst B
  obtain ⟨h1,h2,h3,h4,h5⟩ := core_zero_coefficients b e f (0^2)
    (normalized_core_zero b e f 0 h)
  norm_num at h1 h2 h3 h4 h5
  have q1 : e^5+4-4*b=e^4*f := by linarith only [h1]
  have q2 : e^5+4-4*b^2=e^3*f^2 := by linarith only [h2]
  have hz : (4+e^5)*(b-1)^2=0 := by
    calc
      _ = -(1/4 : ℝ)*(e^5*(e^5+4-4*b^2)-(e^5+4-4*b)^2) := by ring
      _ = 0 := by rw [q1,q2]; ring
  have hb : b=1 := sub_eq_zero.mp
    (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hN))
  subst b
  refine ⟨rfl,?_,rfl⟩
  apply (show Odd 5 by decide).pow_injective
  linarith only [h5]

/-- A nonzero leading coefficient removes the normalization without
requiring rational coefficients or positivity of individual forms. -/
theorem radial_of_first_ne_zero (a b B e f N : ℝ) (ha : a ≠ 0) (hN : N ≠ 0)
    (h : ∀ x y : ℝ,
      2*(a*x^2+b*y^2+B*x*y)^5 + 2*(a*x^2+b*y^2-B*x*y)^5 +
      (e*x^2+f*y^2)^5 = N*(x^2+y^2)^5) : a=b ∧ e=f ∧ B=0 := by
  have hn : N=4*a^5+e^5 := by
    have hh := h 1 0
    norm_num at hh
    linarith only [hh]
  have hn' : 4+(e/a)^5=N/a^5 := by rw [hn]; field_simp
  have hnorm : ∀ x y : ℝ,
      2*(x^2+(b/a)*y^2+(B/a)*x*y)^5 + 2*(x^2+(b/a)*y^2-(B/a)*x*y)^5 +
      ((e/a)*x^2+(f/a)*y^2)^5 = (4+(e/a)^5)*(x^2+y^2)^5 := by
    intro x y
    have hp : x^2+(b/a)*y^2+(B/a)*x*y=(a*x^2+b*y^2+B*x*y)/a := by
      field_simp
    have hm : x^2+(b/a)*y^2-(B/a)*x*y=(a*x^2+b*y^2-B*x*y)/a := by
      field_simp
    have he : (e/a)*x^2+(f/a)*y^2=(e*x^2+f*y^2)/a := by ring
    rw [hn',hp,hm,he,div_pow,div_pow,div_pow]
    field_simp
    linear_combination h x y
  obtain ⟨hb,he,hB⟩ := normalized_radial (b/a) (e/a) (f/a) (B/a)
    (by rw [hn']; exact div_ne_zero hN (pow_ne_zero _ ha)) hnorm
  have hb' : b=a := by simpa using (div_eq_iff ha).mp hb
  have he' : e=f := (div_left_inj' ha).mp he
  have hB' : B=0 := by simpa [ha] using hB
  exact ⟨hb'.symm,he',hB'⟩

/-- Complete binary classification relevant to nonzero norm targets:
the repeated-pair centre is zero, or every output form is radial. -/
theorem zero_center_or_radial (a b B e f N : ℝ) (hN : N ≠ 0)
    (h : ∀ x y : ℝ,
      2*(a*x^2+b*y^2+B*x*y)^5 + 2*(a*x^2+b*y^2-B*x*y)^5 +
      (e*x^2+f*y^2)^5 = N*(x^2+y^2)^5) :
    (a=0 ∧ b=0) ∨ (a=b ∧ e=f ∧ B=0) := by
  by_cases ha : a=0
  · by_cases hb : b=0
    · exact Or.inl ⟨ha,hb⟩
    · have hh : ∀ x y : ℝ,
          2*(b*x^2+a*y^2+B*x*y)^5 + 2*(b*x^2+a*y^2-B*x*y)^5 +
          (f*x^2+e*y^2)^5 = N*(x^2+y^2)^5 := by
        intro x y
        convert h y x using 1 <;> ring
      have hz := (radial_of_first_ne_zero b a B f e N hb hN hh).1
      exact False.elim (hb (hz.trans ha))
  · exact Or.inr (radial_of_first_ne_zero a b B e f N ha hN h)


end
end Erdos322Research.QuinticQuadraticBinaryNorm
