import Submission.QuinticQuarticObstruction

/-! Complete classification of the equal-leading quartic reflection ansatz.
This is a result about one polynomial construction, not a proof of Erdős 322. -/

namespace Erdos322Research.QuinticQuartic

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

def reflectionSum (a b c d e f U : ℝ) : ℝ :=
  2*((U^2+b*U+c)^5+(-U^2+d*U+e)^5)+
  20*U*((U+a)^2*(U^2+b*U+c)^3+(U+f)^2*(-U^2+d*U+e)^3)+
  10*U^2*((U+a)^4*(U^2+b*U+c)+(U+f)^4*(-U^2+d*U+e))

private theorem top_nine (a b c d e f j l N : ℝ)
    (he : ∀ U : ℝ, reflectionSum a b c d e f U+(j*U+l)^5=N) :
    b+d=0 := by
  have h0 := he (0 : ℝ)
  have h1 := he (1 : ℝ)
  have h2 := he (2 : ℝ)
  have h3 := he (3 : ℝ)
  have h4 := he (4 : ℝ)
  have h5 := he (5 : ℝ)
  have h6 := he (6 : ℝ)
  have h7 := he (7 : ℝ)
  have h8 := he (8 : ℝ)
  have h9 := he (9 : ℝ)
  unfold reflectionSum at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hz : (3628800 : ℝ)*(b+d)=0 := by
    linear_combination (-1)*h0 + (9)*h1 + (-36)*h2 + (84)*h3 + (-126)*h4 + (126)*h5 + (-84)*h6 + (36)*h7 + (-9)*h8 + (1)*h9
  linarith

private theorem top_eight (a b c e f j l N : ℝ)
    (he : ∀ U : ℝ, reflectionSum a b c (-b) e f U+(j*U+l)^5=N) :
    c+e+4*a-4*f=0 := by
  have h0 := he (0 : ℝ)
  have h1 := he (1 : ℝ)
  have h2 := he (2 : ℝ)
  have h3 := he (3 : ℝ)
  have h4 := he (4 : ℝ)
  have h5 := he (5 : ℝ)
  have h6 := he (6 : ℝ)
  have h7 := he (7 : ℝ)
  have h8 := he (8 : ℝ)
  unfold reflectionSum at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hz : (403200 : ℝ)*(c+e+4*a-4*f)=0 := by
    linear_combination (1)*h0 + (-8)*h1 + (28)*h2 + (-56)*h3 + (70)*h4 + (-56)*h5 + (28)*h6 + (-8)*h7 + (1)*h8
  linarith

private theorem top_seven (a b c f j l N : ℝ)
    (he : ∀ U : ℝ, reflectionSum a b c (-b) (4*(f-a)-c) f U+(j*U+l)^5=N) :
    (f-a)*(10+2*b-a-f)=0 := by
  have h0 := he (0 : ℝ)
  have h1 := he (1 : ℝ)
  have h2 := he (2 : ℝ)
  have h3 := he (3 : ℝ)
  have h4 := he (4 : ℝ)
  have h5 := he (5 : ℝ)
  have h6 := he (6 : ℝ)
  have h7 := he (7 : ℝ)
  unfold reflectionSum at h0 h1 h2 h3 h4 h5 h6 h7
  have hz : (100800 : ℝ)*((f-a)*(10+2*b-a-f))=0 := by
    linear_combination (-1)*h0 + (7)*h1 + (-21)*h2 + (35)*h3 + (-35)*h4 + (21)*h5 + (-7)*h6 + (1)*h7
  linarith

private theorem top_six (a b c j l N : ℝ)
    (he : ∀ U : ℝ, reflectionSum a b c (-b) (4*(10+2*b-2*a)-c) (10+2*b-a) U+(j*U+l)^5=N) :
    (-a+b+5)*(4*a+b+c+26)=0 := by
  have h0 := he (0 : ℝ)
  have h1 := he (1 : ℝ)
  have h2 := he (2 : ℝ)
  have h3 := he (3 : ℝ)
  have h4 := he (4 : ℝ)
  have h5 := he (5 : ℝ)
  have h6 := he (6 : ℝ)
  unfold reflectionSum at h0 h1 h2 h3 h4 h5 h6
  have hz : (57600 : ℝ)*((-a+b+5)*(4*a+b+c+26))=0 := by
    linear_combination (1)*h0 + (-6)*h1 + (15)*h2 + (-20)*h3 + (15)*h4 + (-6)*h5 + (1)*h6
  linarith


theorem no_centered_affine_fifth_completion (T H j l N : ℝ) (hH : H ≠ 0) :
    ¬ (∀ U : ℝ, centeredSum T H U+(j*U+l)^5=N) := by
  intro he
  by_cases hj : j = 0
  · subst j
    apply no_centered_fifth_power_completion T H 0 0 (N-l^5) hH
    intro U
    have hu := he U
    simp only [zero_mul, zero_add] at hu ⊢
    linarith
  · apply no_centered_fifth_power_completion T H (j^5) (l/j) N hH
    intro U
    have hu := he U
    have ht : j*U+l=j*(U+l/j) := by field_simp
    simpa only [ht, mul_pow] using hu

private theorem reflection_to_centered (a b U : ℝ) :
    reflectionSum a b (-4*a-b-26) (-b)
      (4*(10+2*b-2*a)-(-4*a-b-26)) (10+2*b-a) U =
    centeredSum (b+10) (10+2*b-2*a) (U+b+5) := by
  unfold reflectionSum centeredSum
  ring

theorem reflection_classification (a b c d e f j l N : ℝ)
    (he : ∀ U : ℝ, reflectionSum a b c d e f U+(j*U+l)^5=N) :
    d = -b ∧ f = a ∧ e = -c ∧ j = 0 ∧ N = l^5 := by
  have hd : d = -b := by have hz := top_nine a b c d e f j l N he; linarith
  subst d
  have h_e : e = 4*(f-a)-c := by
    have hz := top_eight a b c e f j l N he
    linarith
  subst e
  have h7 := top_seven a b c f j l N he
  have hf : f = a := by
    by_contra hfa
    have hfa' : f-a ≠ 0 := sub_ne_zero.mpr hfa
    have hsec : 10+2*b-a-f=0 := (mul_eq_zero.mp h7).resolve_left hfa'
    have h_f : f = 10+2*b-a := by linarith
    subst f
    have hnorm : 10+2*b-a-a = 10+2*b-2*a := by ring
    rw [hnorm] at he
    have h6 := top_six a b c j l N he
    have hH : 10+2*b-2*a ≠ 0 := by intro h; apply hfa; linarith
    have hfac : -a+b+5 ≠ 0 := by intro h; apply hH; linarith
    have hc : c = -4*a-b-26 := by
      have hz := (mul_eq_zero.mp h6).resolve_left hfac
      linarith
    subst c
    apply no_centered_affine_fifth_completion (b+10) (10+2*b-2*a)
      j (l-j*(b+5)) N hH
    intro U
    have hu := he (U-b-5)
    rw [reflection_to_centered] at hu
    have ht : U-b-5+b+5=U := by ring
    have hl : j*(U-b-5)+l=j*U+(l-j*(b+5)) := by ring
    simpa only [ht, hl] using hu
  subst f
  have hzero (U : ℝ) : reflectionSum a b c (-b) (4*(a-a)-c) a U = 0 := by
    unfold reflectionSum
    ring
  have hj (U : ℝ) : (j*U+l)^5=N := by simpa only [hzero, zero_add] using he U
  have hj0 := hj 0
  have hj1 := hj 1
  norm_num at hj0 hj1
  have hinj : j+l=l := (show Odd (5 : ℕ) by decide).pow_injective (hj1.trans hj0.symm)
  have hj' : j = 0 := by linarith
  refine ⟨rfl, rfl, ?_, hj', hj0.symm⟩
  ring


def polynomialSum (a b c d e f j l t : ℝ) : ℝ :=
  (t^4+t^3+b*t^2+a*t+c)^5 + (t^4-t^3+b*t^2-a*t+c)^5 +
  (-t^4+t^3+d*t^2+f*t+e)^5 + (-t^4-t^3+d*t^2-f*t+e)^5 +
  (j*t^2+l)^5

theorem polynomialSum_expansion (a b c d e f j l t : ℝ) :
    polynomialSum a b c d e f j l t =
      reflectionSum a b c d e f (t^2)+(j*t^2+l)^5 := by
  unfold polynomialSum reflectionSum
  ring

theorem polynomialSum_classification (a b c d e f j l N : ℝ) :
    (∀ t : ℝ, polynomialSum a b c d e f j l t = N) ↔
      d = -b ∧ f = a ∧ e = -c ∧ j = 0 ∧ N = l^5 := by
  constructor
  · intro he
    let p : Polynomial ℝ :=
      2*((Polynomial.X^2+Polynomial.C b*Polynomial.X+Polynomial.C c)^5+
        (-Polynomial.X^2+Polynomial.C d*Polynomial.X+Polynomial.C e)^5)+
      20*Polynomial.X*((Polynomial.X+Polynomial.C a)^2*
        (Polynomial.X^2+Polynomial.C b*Polynomial.X+Polynomial.C c)^3+
        (Polynomial.X+Polynomial.C f)^2*
        (-Polynomial.X^2+Polynomial.C d*Polynomial.X+Polynomial.C e)^3)+
      10*Polynomial.X^2*((Polynomial.X+Polynomial.C a)^4*
        (Polynomial.X^2+Polynomial.C b*Polynomial.X+Polynomial.C c)+
        (Polynomial.X+Polynomial.C f)^4*
        (-Polynomial.X^2+Polynomial.C d*Polynomial.X+Polynomial.C e))+
      (Polynomial.C j*Polynomial.X+Polynomial.C l)^5
    have heval (U : ℝ) : p.eval U = reflectionSum a b c d e f U+(j*U+l)^5 := by
      simp [p, reflectionSum]
    have hp : p = Polynomial.C N := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.Ici_infinite (0 : ℝ)).mono
      intro U hU
      change p.eval U = (Polynomial.C N).eval U
      rw [heval, Polynomial.eval_C]
      have hu := he (Real.sqrt U)
      rw [polynomialSum_expansion, Real.sq_sqrt hU] at hu
      exact hu
    apply reflection_classification a b c d e f j l N
    intro U
    rw [← heval, hp, Polynomial.eval_C]
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩ t
    unfold polynomialSum
    ring

theorem no_positive_polynomialSum (a b c d e f j l N t : ℝ)
    (hpos : 0 < t^4+t^3+b*t^2+a*t+c)
    (hnonneg : 0 ≤ -t^4-t^3+d*t^2-f*t+e) :
    ¬ (∀ u : ℝ, polynomialSum a b c d e f j l u = N) := by
  intro he
  obtain ⟨hd, hf, he', _, _⟩ := (polynomialSum_classification a b c d e f j l N).mp he
  rw [hd, hf, he'] at hnonneg
  nlinarith

end
end Erdos322Research.QuinticQuartic
