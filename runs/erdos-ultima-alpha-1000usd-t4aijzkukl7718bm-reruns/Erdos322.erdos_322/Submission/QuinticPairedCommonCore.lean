import Submission.QuinticPairedMoments

/-! A complete obstruction to a common-core quadratic quintic identity with
paired opposite linear coefficients. This is not a settlement of Erdős 322. -/
namespace Erdos322Research.QuinticPairedCommonCore
noncomputable section
open Polynomial QuinticPairedMoments
set_option Elab.async false
set_option maxHeartbeats 1000000

private def expanded (n l e m f h A : ℚ) : ℚ[X] :=
  C n+C (5*l)*X+C (10*e-5*h*n)*X^2+C (10*m-20*h*l)*X^3+
  C (10*h^2*n-30*h*e+5*f)*X^4+C (30*h^2*l-20*h*m)*X^5+
  C (-10*h^3*n+30*h^2*e-5*h*f)*X^6+C (-20*h^3*l+10*h^2*m)*X^7+
  C (5*h^4*n-10*h^3*e)*X^8+C (5*h^4*l)*X^9+C (A^5-h^5*n)*X^10

private theorem coefficient_relations {a b c d u v h A N : ℚ}
    (hp : ∀ t : ℚ,
      (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)-u*t)^5+
      (c*(1-h*t^2)+v*t)^5+(d*(1-h*t^2)-v*t)^5+(A*t^2)^5=N) :
    let n := a^5+b^5+c^5+d^5
    let l := (a^4-b^4)*u+(c^4-d^4)*v
    let e := (a^3+b^3)*u^2+(c^3+d^3)*v^2
    let m := (a^2-b^2)*u^3+(c^2-d^2)*v^3
    let f := (a+b)*u^4+(c+d)*v^4
    n=N ∧ l=0 ∧ 2*e-h*n=0 ∧ m=0 ∧ f-h^2*n=0 ∧ A^5-h^5*n=0 := by
  dsimp only
  let n := a^5+b^5+c^5+d^5
  let l := (a^4-b^4)*u+(c^4-d^4)*v
  let e := (a^3+b^3)*u^2+(c^3+d^3)*v^2
  let m := (a^2-b^2)*u^3+(c^2-d^2)*v^3
  let f := (a+b)*u^4+(c+d)*v^4
  have he : expanded n l e m f h A = C N := by
    apply Polynomial.funext
    intro t
    simp only [expanded,eval_add,eval_mul,eval_pow,eval_C,eval_X]
    dsimp [n,l,e,m,f]
    linear_combination hp t
  have h0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) he
  have h1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) he
  have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) he
  have h3 := congrArg (fun p : ℚ[X] ↦ p.coeff 3) he
  have h4 := congrArg (fun p : ℚ[X] ↦ p.coeff 4) he
  have h10 := congrArg (fun p : ℚ[X] ↦ p.coeff 10) he
  simp only [expanded,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    at h0 h1 h2 h3 h4 h10
  norm_num at h0 h1 h2 h3 h4 h10
  have hl : l=0 := by linarith
  have hm : m=0 := by rw [hl] at h3; linarith
  have hE : 2*e-h*n=0 := by linarith
  have hF : f-h^2*n=0 := by linear_combination h4/5+3*h*hE
  exact ⟨h0,hl,hE,hm,hF,h10⟩

/-- The whole paired-linear common-core family is constant whenever its four
centres are positive rational numbers. No leading seed is prescribed. -/
theorem positive_identity_constant {a b c d u v h A N : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : ∀ t : ℚ,
      (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)-u*t)^5+
      (c*(1-h*t^2)+v*t)^5+(d*(1-h*t^2)-v*t)^5+(A*t^2)^5=N) :
    h=0 ∧ u=0 ∧ v=0 ∧ A=0 ∧ N=a^5+b^5+c^5+d^5 := by
  obtain ⟨h0,h1,h2,h3,h4,h10⟩ := coefficient_relations hp
  let n := a^5+b^5+c^5+d^5
  let e := (a^3+b^3)*u^2+(c^3+d^3)*v^2
  let f := (a+b)*u^4+(c+d)*v^4
  have hn : 0 < n := by dsimp [n]; positivity
  have h2' : 2*e-h*n=0 := h2
  have h4' : f-h^2*n=0 := h4
  have hE : momentEven a b c d u v=0 := by
    change n*f-4*e^2=0
    linear_combination n*h4'-(2*e+h*n)*h2'
  have huv : u=0 ∧ v=0 := by
    by_cases hh : h=0
    · have he : e=0 := by rw [hh] at h2'; linarith
      have hab3 : 0 < a^3+b^3 := by positivity
      have hcd3 : 0 < c^3+d^3 := by positivity
      have hU : (a^3+b^3)*u^2=0 := by
        have hvn : 0 ≤ (c^3+d^3)*v^2 := by positivity
        dsimp [e] at he
        nlinarith [mul_nonneg hab3.le (sq_nonneg u)]
      have hV : (c^3+d^3)*v^2=0 := by
        dsimp [e] at he
        linarith
      exact ⟨eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hU).resolve_left hab3.ne'),
        eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hV).resolve_left hcd3.ne')⟩
    · have hf : n=(A/h)^5 := by
        field_simp
        linear_combination -h10
      exact rational_paired_slopes_zero ha hb hc hd hf h1 h3 hE
  obtain ⟨hu,hv⟩ := huv
  have hh : h=0 := by
    have he : e=0 := by simp [e,hu,hv]
    rw [he] at h2'
    have hh' : h*n=0 := by linarith
    exact (mul_eq_zero.mp hh').resolve_right hn.ne'
  have hA : A=0 := by
    rw [hh] at h10
    norm_num at h10
    exact h10
  exact ⟨hh,hu,hv,hA,h0.symm⟩

private def corrected (n l e m f h A C₀ : ℚ) : ℚ[X] :=
  expanded n l e m f h A + C (C₀^5)+C (5*C₀^4*A)*X^2+
    C (10*C₀^3*A^2)*X^4+C (10*C₀^2*A^3)*X^6+C (5*C₀*A^4)*X^8

private theorem shifted_relations {a b c d u v h A C₀ N : ℚ}
    (hp : ∀ t : ℚ,
      (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)-u*t)^5+
      (c*(1-h*t^2)+v*t)^5+(d*(1-h*t^2)-v*t)^5+(C₀+A*t^2)^5=N) :
    let n := a^5+b^5+c^5+d^5
    let e := (a^3+b^3)*u^2+(c^3+d^3)*v^2
    n+C₀^5=N ∧ 2*e-h*n+C₀^4*A=0 ∧
      h^4*n-2*h^3*e+C₀*A^4=0 ∧ A^5-h^5*n=0 := by
  dsimp only
  let n := a^5+b^5+c^5+d^5
  let l := (a^4-b^4)*u+(c^4-d^4)*v
  let e := (a^3+b^3)*u^2+(c^3+d^3)*v^2
  let m := (a^2-b^2)*u^3+(c^2-d^2)*v^3
  let f := (a+b)*u^4+(c+d)*v^4
  have he : corrected n l e m f h A C₀ = C N := by
    apply Polynomial.funext
    intro t
    simp only [corrected,expanded,eval_add,eval_mul,eval_pow,eval_C,eval_X]
    dsimp [n,l,e,m,f]
    linear_combination hp t
  have h0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) he
  have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) he
  have h8 := congrArg (fun p : ℚ[X] ↦ p.coeff 8) he
  have h10 := congrArg (fun p : ℚ[X] ↦ p.coeff 10) he
  simp only [corrected,expanded,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    at h0 h2 h8 h10
  norm_num at h0 h2 h8 h10
  exact ⟨h0,by linarith,by linarith,h10⟩

private theorem curvature_or_last_constant_zero {n e h A C₀ N : ℚ}
    (hn : n ≠ 0) (hN : N ≠ 0)
    (h0 : n+C₀^5=N) (h2 : 2*e-h*n+C₀^4*A=0)
    (h8 : h^4*n-2*h^3*e+C₀*A^4=0) (h10 : A^5-h^5*n=0) :
    h=0 ∨ C₀=0 := by
  by_cases hh : h=0
  · exact Or.inl hh
  · right
    by_contra hC
    have hA : A ≠ 0 := by
      intro hz
      rw [hz] at h10
      have he : h^5*n=0 := by simpa using h10
      exact mul_ne_zero (pow_ne_zero _ hh) hn he
    have he : C₀*A*((C₀*h)^3+A^3)=0 := by
      linear_combination h^3*h2+h8
    have hcub : (C₀*h)^3=(-A)^3 := by
      have hz := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hC hA)
      nlinarith only [hz]
    have hCA : C₀*h = -A := (show Odd 3 by decide).pow_injective hcub
    have hpow : C₀^5*h^5 = -A^5 := by
      calc
        C₀^5*h^5 = (C₀*h)^5 := by ring
        _ = (-A)^5 := by rw [hCA]
        _ = -A^5 := by ring
    have hz : h^5*N=0 := by
      linear_combination -h^5*h0-h10+hpow
    exact mul_ne_zero (pow_ne_zero _ hh) hN hz

/-- Allowing an arbitrary constant term in the fifth quadratic does not restore
nonconstant identities at any nonzero target. The four other centres remain
positive, but no sign restriction is placed on the fifth centre. -/
theorem positive_nonzero_identity_constant {a b c d u v h A C₀ N : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hN : N ≠ 0)
    (hp : ∀ t : ℚ,
      (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)-u*t)^5+
      (c*(1-h*t^2)+v*t)^5+(d*(1-h*t^2)-v*t)^5+(C₀+A*t^2)^5=N) :
    h=0 ∧ u=0 ∧ v=0 ∧ A=0 ∧ N=a^5+b^5+c^5+d^5+C₀^5 := by
  obtain ⟨h0,h2,h8,h10⟩ := shifted_relations hp
  have hn : a^5+b^5+c^5+d^5 ≠ 0 := ne_of_gt (by positivity)
  rcases curvature_or_last_constant_zero hn hN h0 h2 h8 h10 with hh | hC
  · have hA : A=0 := by rw [hh] at h10; norm_num at h10; exact h10
    have hp' : ∀ t : ℚ,
        (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)-u*t)^5+
        (c*(1-h*t^2)+v*t)^5+(d*(1-h*t^2)-v*t)^5+(A*t^2)^5=N-C₀^5 := by
      intro t
      have ht := hp t
      rw [hA] at ht ⊢
      norm_num at ht ⊢
      linarith
    obtain ⟨_,hu,hv,_,_⟩ := positive_identity_constant ha hb hc hd hp'
    exact ⟨hh,hu,hv,hA,h0.symm⟩
  · subst C₀
    have hp' := positive_identity_constant ha hb hc hd (by simpa using hp)
    simpa using hp'

/-- A zero sum obtained by splitting four terms into opposite pairs. -/
def OppositePairs (u v w z : ℚ) : Prop :=
  (v = -u ∧ z = -w) ∨ (w = -u ∧ z = -v) ∨ (z = -u ∧ w = -v)

private theorem general_odd_fifth_zero {a b c d u v w z h A C₀ N : ℚ}
    (hp : ∀ t : ℚ,
      (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)+v*t)^5+
      (c*(1-h*t^2)+w*t)^5+(d*(1-h*t^2)+z*t)^5+(C₀+A*t^2)^5=N) :
    u^5+v^5+w^5+z^5=0 := by
  let n := a^5+b^5+c^5+d^5
  let l := a^4*u+b^4*v+c^4*w+d^4*z
  let e := a^3*u^2+b^3*v^2+c^3*w^2+d^3*z^2
  let m := a^2*u^3+b^2*v^3+c^2*w^3+d^2*z^3
  let f := a*u^4+b*v^4+c*w^4+d*z^4
  let g := u^5+v^5+w^5+z^5
  have he : corrected n l e m f h A C₀+C g*X^5=C N := by
    apply Polynomial.funext
    intro t
    simp only [corrected,expanded,eval_add,eval_mul,eval_pow,eval_C,eval_X]
    dsimp [n,l,e,m,f,g]
    linear_combination hp t
  have h1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) he
  have h3 := congrArg (fun p : ℚ[X] ↦ p.coeff 3) he
  have h5 := congrArg (fun p : ℚ[X] ↦ p.coeff 5) he
  simp only [corrected,expanded,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    at h1 h3 h5
  norm_num at h1 h3 h5
  have hl : l=0 := by linarith
  have hm : m=0 := by rw [hl] at h3; linarith
  rw [hl,hm] at h5
  simpa only [mul_zero,sub_self,zero_add] using h5

/-- A nonconstant rational identity in the general common-core family would
supply a four-term fifth-power zero not explained by opposite pairs. This is
an implication, not an existence theorem for such zeros. -/
theorem nonzero_curvature_gives_nonpaired_fifths {a b c d u v w z h A C₀ N : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hh : h ≠ 0) (hN : N ≠ 0)
    (hp : ∀ t : ℚ,
      (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)+v*t)^5+
      (c*(1-h*t^2)+w*t)^5+(d*(1-h*t^2)+z*t)^5+(C₀+A*t^2)^5=N) :
    u^5+v^5+w^5+z^5=0 ∧ ¬OppositePairs u v w z := by
  refine ⟨general_odd_fifth_zero hp,?_⟩
  rintro (⟨hv,hz⟩ | ⟨hw,hz⟩ | ⟨hz,hw⟩)
  · have hp' : ∀ t : ℚ,
        (a*(1-h*t^2)+u*t)^5+(b*(1-h*t^2)-u*t)^5+
        (c*(1-h*t^2)+w*t)^5+(d*(1-h*t^2)-w*t)^5+(C₀+A*t^2)^5=N := by
      intro t
      have ht := hp t
      rw [hv,hz] at ht
      linear_combination ht
    exact hh (positive_nonzero_identity_constant ha hb hc hd hN hp').1
  · have hp' : ∀ t : ℚ,
        (a*(1-h*t^2)+u*t)^5+(c*(1-h*t^2)-u*t)^5+
        (b*(1-h*t^2)+v*t)^5+(d*(1-h*t^2)-v*t)^5+(C₀+A*t^2)^5=N := by
      intro t
      have ht := hp t
      rw [hw,hz] at ht
      linear_combination ht
    exact hh (positive_nonzero_identity_constant ha hc hb hd hN hp').1
  · have hp' : ∀ t : ℚ,
        (a*(1-h*t^2)+u*t)^5+(d*(1-h*t^2)-u*t)^5+
        (b*(1-h*t^2)+v*t)^5+(c*(1-h*t^2)-v*t)^5+(C₀+A*t^2)^5=N := by
      intro t
      have ht := hp t
      rw [hz,hw] at ht
      linear_combination ht
    exact hh (positive_nonzero_identity_constant ha hd hb hc hN hp').1

end
end Erdos322Research.QuinticPairedCommonCore
