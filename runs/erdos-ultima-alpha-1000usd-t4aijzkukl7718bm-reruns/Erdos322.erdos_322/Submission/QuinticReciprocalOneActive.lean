import FormalConjecturesUtil

/-! Exact algebra for the one-active-slope reciprocal quintic model.
The elliptic reduction below is not a rational-point classification, and
none of these results is an unrestricted representation-count estimate. -/
namespace Erdos322Research.QuinticReciprocalOneActive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- Here the repeated centre is normalized to one, while the other two
centres are `m+h` and `m-h`. These are its two nonautomatic even moments. -/
def Moments (m h u : ℚ) : Prop :=
  4*u^2-2-2*m^5-4*m^3*h^2+6*m*h^4=0 ∧
  2-6*u^2+u^4+2*m^5-4*m^3*h^2+2*m*h^4=0

/-- Denominator-free elimination, including every exceptional chart. -/
theorem elimination {m h u : ℚ} (hm : Moments m h u) :
    32*(u^4-6*u^2+2)*m^5+(3*u^4-22*u^2+8)^2=0 ∧
    32*(u^4-6*u^2+2)*m^3*h^2-
      u^2*(u^2-2)*(3*u^4-22*u^2+8)=0 ∧
    32*(u^4-6*u^2+2)*m*h^4+u^4*(u^2-2)^2=0 ∧
    (3*u^4-22*u^2+8)*h^2+m^2*u^2*(u^2-2)=0 := by
  obtain ⟨h1,h2⟩ := hm
  have hs : u^4-2*u^2-8*m^3*h^2+8*m*h^4=0 := by
    linear_combination h1+h2
  let F := -1+(11/4)*u^2-(3/8)*u^4
  let G := u^2/4-u^4/8
  have hF : m^5-m^3*h^2-F=0 := by
    dsimp [F]
    linear_combination -h1/2+3*hs/8
  have hG : m*h^4-m^3*h^2-G=0 := by
    dsimp [G]
    linear_combination hs/8
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (norm := (dsimp [F,G]; ring_nf))
      64*(m^3*h^2-F)*hF+64*m^5*hG
  · linear_combination (norm := (dsimp [F,G]; ring_nf))
      64*m*h^4*hF+64*(m^3*h^2+F)*hG
  · linear_combination (norm := (dsimp [F,G]; ring_nf))
      64*(m^3*h^2-G)*hG+64*m*h^4*hF
  · linear_combination (m^2+3*h^2)*hs-4*h^2*h1

/-- The apparent denominator in the elimination never vanishes. -/
theorem denominator_ne_zero {m h u : ℚ} (hm : Moments m h u) :
    u^4-6*u^2+2 ≠ 0 := by
  intro hd
  have he := (elimination hm).1
  rw [hd] at he
  have hk : 3*u^4-22*u^2+8=0 := by nlinarith only [he]
  have hu : u^2=1/2 := by linear_combination (3*hd-hk)/4
  nlinarith only [hd,hu,sq_nonneg (u^2-1/2)]

/-- The target is also determined by the squared slope. -/
theorem target_relation {m h u N : ℚ} (hm : Moments m h u)
    (hN : N=2+(m+h)^5+(m-h)^5) :
    N*(u^4-6*u^2+2)=u^6*(u^2-8) := by
  obtain ⟨h1,h2⟩ := hm
  have hs : u^4-2*u^2-8*m^3*h^2+8*m*h^4=0 := by
    linear_combination h1+h2
  have hn : N=2*u^4+32*m*h^4 := by
    linear_combination hN-h1-2*hs
  have he := (elimination (show Moments m h u from ⟨h1,h2⟩)).2.2.1
  linear_combination he+(u^4-6*u^2+2)*hn

/-- A point on a genus-two curve is necessary for this rational model. -/
theorem hyperelliptic_relation {m h u : ℚ} (hm : Moments m h u)
    (hm0 : m ≠ 0) (hu0 : u ≠ 0) :
    (h*(3*u^4-22*u^2+8)/(m*u))^2 =
      -(u^2-2)*(3*u^4-22*u^2+8) := by
  have he := (elimination hm).2.2.2
  field_simp
  linear_combination (3*u^4-22*u^2+8)*he

/-- The relevant elliptic quotient is `y²=x³-7x²-12x`.
This theorem makes no claim about its rational rank or its rational points. -/
theorem elliptic_relation {m h u : ℚ} (hm : Moments m h u)
    (hm0 : m ≠ 0) (hu0 : u ≠ 0) :
    (2*h*(3*u^4-22*u^2+8)/(m*u^4))^2 =
      (4/u^2-2)^3-7*(4/u^2-2)^2-12*(4/u^2-2) := by
  have he := (elimination hm).2.2.2
  field_simp
  linear_combination 4*(3*u^4-22*u^2+8)*he


open Polynomial
private def expanded (n f g e : ℚ) : ℚ[X] :=
  C n+C (5*f)*X^2+C (10*g)*X^4+C (-10*g)*X^6+
    C (-5*f)*X^8+C (e^5-n)*X^10

/-- Coefficient extraction connects the elimination to the actual normalized
one-active-slope reciprocal identity. -/
theorem identity_relations {m h u e N : ℚ}
    (hp : ∀ t : ℚ,
      (1-t^2+u*t)^5+(1-t^2-u*t)^5+
      (-(m+h)*t^2+(m-h))^5+(-(m-h)*t^2+(m+h))^5+(e*t^2)^5=N) :
    Moments m h u ∧ N=2+(m+h)^5+(m-h)^5 ∧ e^5=N := by
  let n := 2+(m+h)^5+(m-h)^5
  let f := 4*u^2-2-2*m^5-4*m^3*h^2+6*m*h^4
  let g := 2-6*u^2+u^4+2*m^5-4*m^3*h^2+2*m*h^4
  have he : expanded n f g e=C N := by
    apply Polynomial.funext
    intro t
    simp only [expanded,eval_add,eval_mul,eval_pow,eval_C,eval_X]
    dsimp [n,f,g]
    linear_combination hp t
  have h0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) he
  have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) he
  have h4 := congrArg (fun p : ℚ[X] ↦ p.coeff 4) he
  have h10 := congrArg (fun p : ℚ[X] ↦ p.coeff 10) he
  simp only [expanded,coeff_add,coeff_C_mul_X_pow,coeff_C] at h0 h2 h4 h10
  norm_num at h0 h2 h4 h10
  refine ⟨⟨?_,?_⟩,h0.symm,?_⟩
  · change f=0
    linarith only [h2]
  · change g=0
    linarith only [h4]
  · linarith only [h10,h0]

end
end Erdos322Research.QuinticReciprocalOneActive
