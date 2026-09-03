import FormalConjecturesUtil

/-! A real moment inequality for the reciprocal-quadratic quintic ansatz.
This is a restricted construction obstruction, not a representation-count bound. -/
namespace Erdos322Research.QuinticReciprocalMomentCertificate

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- Two positive weights with oppositely ordered nodes and slopes have the
corresponding reversed weighted-mean inequality. -/
private theorem weighted_mean {p q r s a b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (horder : (r-s)*(a-b) ≤ 0)
    (hmean : 8*(p*r*a+q*s*b)=p*r+q*s) :
    p+q ≤ 8*(p*a+q*b) := by
  have hcov : p*q*((r-s)*(a-b)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp.le hq.le) horder
  have hid : (p*r+q*s)*(8*(p*a+q*b)-(p+q)) =
      -8*p*q*((r-s)*(a-b)) := by
    linear_combination (p+q)*hmean
  have hprod : 0 ≤ (p*r+q*s)*(8*(p*a+q*b)-(p+q)) := by
    rw [hid]
    nlinarith only [hcov]
  have hpos : 0 < p*r+q*s := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hpos).mp hprod
  linarith

/-- The normalized reciprocal moments are incompatible. The odd relation
forces both slopes below one half and orders them oppositely to the nodes. -/
theorem moment_residual_neg {p q r s a b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (ha : 0 < a) (hb : 0 < b)
    (hodd : (s+1)*(1/2-a)=(r+1)*(1/2-b))
    (hmean : 8*(p*r*a+q*s*b)=p*r+q*s) :
    p*(1-12*a+8*a^2)+q*(1-12*b+8*b^2) < 0 := by
  have hr1 : 0 < r+1 := by linarith
  have hs1 : 0 < s+1 := by linarith
  have hA : a < 1/2 := by
    by_contra hn
    have ha' : 1/2 ≤ a := le_of_not_gt hn
    have hz : (r+1)*(1/2-b) ≤ 0 := by
      rw [←hodd]
      exact mul_nonpos_of_nonneg_of_nonpos hs1.le (by linarith)
    have hb' : 1/2 ≤ b := by
      have hh := nonpos_of_mul_nonpos_right hz hr1
      linarith
    have hpa := mul_le_mul_of_nonneg_left ha' (mul_nonneg hp.le hr.le)
    have hqb := mul_le_mul_of_nonneg_left hb' (mul_nonneg hq.le hs.le)
    have hpos : 0 < p*r+q*s := by positivity
    nlinarith only [hpa,hqb,hmean,hpos]
  have hB : b < 1/2 := by
    have hh : 0 < (r+1)*(1/2-b) := by
      rw [←hodd]
      exact mul_pos hs1 (by linarith)
    have hh' := (mul_pos_iff_of_pos_left hr1).mp hh
    linarith
  have hi : (r+1)*((r-s)*(a-b)) = -(r-s)^2*(1/2-a) := by
    linear_combination -(r-s)*hodd
  have horder : (r-s)*(a-b) ≤ 0 := by
    have hh : (r+1)*((r-s)*(a-b)) ≤ 0 := by
      rw [hi]
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [sq_nonneg (r-s)])
        (by linarith)
    exact nonpos_of_mul_nonpos_right hh hr1
  have hm := weighted_mean hp hq hr hs horder hmean
  have hfa : 1-12*a+8*a^2 < 1-8*a := by
    nlinarith only [mul_pos ha (show 0 < 1/2-a by linarith)]
  have hfb : 1-12*b+8*b^2 < 1-8*b := by
    nlinarith only [mul_pos hb (show 0 < 1/2-b by linarith)]
  have hpa := mul_lt_mul_of_pos_left hfa hp
  have hqb := mul_lt_mul_of_pos_left hfb hq
  nlinarith only [hpa,hqb,hm]


/-- A denominator-free odd relation and the second even moment force a
strictly negative fourth even residual. The squared-slope ratio need not be
introduced, so this also covers the singular ratio chart. -/
theorem normalized_reciprocal_residual_neg {b c d u v : ℝ}
    (hc : 0 < c) (hB : b^2 < 1) (hD : d^2 < c^2)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hodd : (c^2+d^2)*((1-b^2)/2-u^2) =
      (1+b^2)*((c^2-d^2)/2-v^2))
    (heven : 8*((1+3*b^2)*u^2+(c^3+3*c*d^2)*v^2) =
      (1-b^2)*(1+3*b^2)+(c^2-d^2)*(c^3+3*c*d^2)) :
    (1-b^2)^2-12*(1-b^2)*u^2+8*u^4+
      c*((c^2-d^2)^2-12*(c^2-d^2)*v^2+8*v^4) < 0 := by
  have h1 : 0 < 1-b^2 := sub_pos.mpr hB
  have h2 : 0 < c^2-d^2 := sub_pos.mpr hD
  have h1n := h1.ne'
  have h2n := h2.ne'
  have hr : 0 < (1+3*b^2)/(1-b^2) := by positivity
  have hs : 0 < (c^2+3*d^2)/(c^2-d^2) := by
    apply div_pos _ h2
    have hh := sq_pos_of_pos hc
    nlinarith only [hh,sq_nonneg d]
  have ha : 0 < u^2/(1-b^2) := div_pos (sq_pos_of_ne_zero hu) h1
  have hb : 0 < v^2/(c^2-d^2) := div_pos (sq_pos_of_ne_zero hv) h2
  have ho : ((c^2+3*d^2)/(c^2-d^2)+1)*(1/2-u^2/(1-b^2)) =
      ((1+3*b^2)/(1-b^2)+1)*(1/2-v^2/(c^2-d^2)) := by
    field_simp
    linear_combination 4*hodd
  have hm : 8*((1-b^2)^2*((1+3*b^2)/(1-b^2))*(u^2/(1-b^2))+
      (c*(c^2-d^2)^2)*((c^2+3*d^2)/(c^2-d^2))*(v^2/(c^2-d^2))) =
      (1-b^2)^2*((1+3*b^2)/(1-b^2))+
      (c*(c^2-d^2)^2)*((c^2+3*d^2)/(c^2-d^2)) := by
    field_simp
    linear_combination heven
  have hn := moment_residual_neg (sq_pos_of_pos h1)
    (mul_pos hc (sq_pos_of_pos h2)) hr hs ha hb ho hm
  convert hn using 1 <;> field_simp

/-- In the reciprocal model with positive centres, each nonzero slope must
belong to a pair of equal centres. No division by the slope-ratio eliminant
is used. This does not exclude the remaining zero-slope branches. -/
theorem normalized_moments_force_paired {b c d u v : ℝ}
    (hc : 0 < c) (hB : b^2 < 1) (hD : d^2 < c^2)
    (hodd1 : b*(1+b^2)*u+c*d*(c^2+d^2)*v=0)
    (hodd3 : b*u*((1-b^2)/2-u^2)+c*d*v*((c^2-d^2)/2-v^2)=0)
    (heven2 : 8*((1+3*b^2)*u^2+(c^3+3*c*d^2)*v^2) =
      (1-b^2)*(1+3*b^2)+(c^2-d^2)*(c^3+3*c*d^2))
    (heven4 : (1-b^2)^2-12*(1-b^2)*u^2+8*u^4+
      c*((c^2-d^2)^2-12*(c^2-d^2)*v^2+8*v^4)=0) :
    b*u=0 ∧ d*v=0 := by
  have hb1 : 0 < 1+b^2 := by positivity
  have hcd : 0 < c^2+d^2 := by
    have hh := sq_pos_of_pos hc
    nlinarith only [hh,sq_nonneg d]
  have hbu : b*u=0 := by
    by_contra hbu
    have hu : u ≠ 0 := fun hh ↦ hbu (by rw [hh,mul_zero])
    have hdv : d*v ≠ 0 := by
      intro hh
      have hz : (1+b^2)*(b*u)=0 := by
        linear_combination hodd1-c*(c^2+d^2)*hh
      exact mul_ne_zero hb1.ne' hbu hz
    have hv : v ≠ 0 := fun hh ↦ hdv (by rw [hh,mul_zero])
    have hprod : c*(d*v)*((c^2+d^2)*((1-b^2)/2-u^2)-
        (1+b^2)*((c^2-d^2)/2-v^2))=0 := by
      linear_combination ((1-b^2)/2-u^2)*hodd1-(1+b^2)*hodd3
    have ho : (c^2+d^2)*((1-b^2)/2-u^2) =
        (1+b^2)*((c^2-d^2)/2-v^2) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc.ne' hdv))
    have hn := normalized_reciprocal_residual_neg hc hB hD hu hv ho heven2
    linarith only [hn,heven4]
  refine ⟨hbu,?_⟩
  have hz : (c*(c^2+d^2))*(d*v)=0 := by
    linear_combination hodd1-(1+b^2)*hbu
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hc.ne' hcd.ne')


open Polynomial
private def expanded (n o₁ o₃ e₂ e₄ e : ℝ) : ℝ[X] :=
  C n+C (-(5/2)*o₁)*X+C ((5/16)*e₂)*X^2+C (10*o₃)*X^3+
  C ((5/8)*e₄)*X^4+C (-(5/8)*e₄)*X^6+C (-10*o₃)*X^7+
  C (-(5/16)*e₂)*X^8+C ((5/2)*o₁)*X^9+C (e^5-n)*X^10

/-- The normalized reciprocal polynomial identity forces its active slope
pairs to have equal centres. This is only a necessary condition on this
particular construction. -/
theorem normalized_reciprocal_identity_paired {b c d u v e N : ℝ}
    (hc : 0 < c) (hB : b^2 < 1) (hD : d^2 < c^2)
    (hp : ∀ t : ℝ,
      (-(1+b)/2*t^2+u*t+(1-b)/2)^5+
      (-(1-b)/2*t^2-u*t+(1+b)/2)^5+
      (-(c+d)/2*t^2+v*t+(c-d)/2)^5+
      (-(c-d)/2*t^2-v*t+(c+d)/2)^5+(e*t^2)^5=N) :
    b*u=0 ∧ d*v=0 := by
  let n := (1+10*b^2+5*b^4+c^5+10*c^3*d^2+5*c*d^4)/16
  let o₁ := b*(1+b^2)*u+c*d*(c^2+d^2)*v
  let o₃ := b*u*((1-b^2)/2-u^2)+c*d*v*((c^2-d^2)/2-v^2)
  let e₂ := 8*((1+3*b^2)*u^2+(c^3+3*c*d^2)*v^2)-
    ((1-b^2)*(1+3*b^2)+(c^2-d^2)*(c^3+3*c*d^2))
  let e₄ := (1-b^2)^2-12*(1-b^2)*u^2+8*u^4+
    c*((c^2-d^2)^2-12*(c^2-d^2)*v^2+8*v^4)
  have he : expanded n o₁ o₃ e₂ e₄ e=C N := by
    apply Polynomial.funext
    intro t
    simp only [expanded,eval_add,eval_mul,eval_pow,eval_C,eval_X]
    dsimp [n,o₁,o₃,e₂,e₄]
    linear_combination hp t
  have h1 := congrArg (fun p : ℝ[X] ↦ p.coeff 1) he
  have h2 := congrArg (fun p : ℝ[X] ↦ p.coeff 2) he
  have h3 := congrArg (fun p : ℝ[X] ↦ p.coeff 3) he
  have h4 := congrArg (fun p : ℝ[X] ↦ p.coeff 4) he
  simp only [expanded,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  apply normalized_moments_force_paired hc hB hD
  · change o₁=0
    linarith only [h1]
  · change o₃=0
    linarith only [h3]
  · exact sub_eq_zero.mp (show e₂=0 by linarith only [h2])
  · change e₄=0
    linarith only [h4]

end
end Erdos322Research.QuinticReciprocalMomentCertificate
