import Submission.QuinticJointCoefficients
import Submission.QuinticJointGeneralCertificate
import Submission.QuinticTwoQuadraticParity
import Submission.QuinticThreeLinearAbsorption
import Submission.QuinticJointReflectedAbsorption

/-! Nonexistence of an arbitrary three-quadratic joint absorption of the
weighted quintic identity. This is a construction obstruction only, not a
representation-count bound or a settlement of the original conjecture. -/
namespace Erdos322Research.QuinticJointGeneralAbsorption
open QuinticJointCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem no_fifth_six (x : ℚ) : x^5 ≠ 6 := by
  intro hx
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
  have h3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  have h2 : padicValRat 3 (2 : ℚ) = 0 := by
    change padicValRat 3 (↑(2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]
    rfl
  have h6 : padicValRat 3 (6 : ℚ) = 1 := by
    rw [show (6 : ℚ) = 2*3 by norm_num,
      padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0), h2, h3]
    norm_num
  have h := congrArg (padicValRat 3) hx
  rw [padicValRat.pow hx0, h6] at h
  omega

private theorem all_even_impossible (a0 c0 a1 c1 a2 c2 : ℚ)
    (h : ∀ t : ℚ, (a0*t^2+c0)^5+(a1*t^2+c1)^5+(a2*t^2+c2)^5 =
      6*(1-2*t^2)^5+8*(2*t^2)^5) : False := by
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10⟩ :=
    coefficient_equations a0 0 c0 a1 0 c1 a2 0 c2 (by simpa using h)
  norm_num [f0, f2, f4, f6, f8, f10] at h0 h2 h4 h6 h8 h10
  apply QuinticThreeLinearAbsorption.coefficients_impossible ![a0,a1,a2] ![c0,c1,c2]
  all_goals simp only [Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · linear_combination h0
  · linear_combination h2/5
  · linear_combination h4/10
  · linear_combination h6/10
  · linear_combination h8/5
  · linear_combination h10

private theorem last_linear_zero (a0 c0 a1 c1 a2 b2 c2 : ℚ)
    (h : ∀ t : ℚ, (a0*t^2+c0)^5+(a1*t^2+c1)^5+(a2*t^2+b2*t+c2)^5 =
      6*(1-2*t^2)^5+8*(2*t^2)^5) : b2 = 0 := by
  have h1 := h 1
  have hm := h (-1)
  norm_num at h1 hm
  have hp : (a2+b2+c2)^5 = (a2-b2+c2)^5 := by
    linear_combination h1-hm
  have he := (show Odd 5 by decide).pow_injective hp
  linarith

/-- In this model, even one even quadratic already forces a contradiction. -/
theorem even_first_impossible (a0 c0 a1 b1 c1 a2 b2 c2 : ℚ)
    (h : ∀ t : ℚ, (a0*t^2+c0)^5+(a1*t^2+b1*t+c1)^5+(a2*t^2+b2*t+c2)^5 =
      6*(1-2*t^2)^5+8*(2*t^2)^5) : False := by
  by_cases hb1 : b1 = 0
  · subst b1
    have hb2 := last_linear_zero a0 c0 a1 c1 a2 b2 c2 (by simpa using h)
    subst b2
    exact all_even_impossible a0 c0 a1 c1 a2 c2 (by simpa using h)
  by_cases hb2 : b2 = 0
  · subst b2
    have hb1 := last_linear_zero a0 c0 a2 c2 a1 b1 c1 (by
      intro t
      have ht := h t
      simp only [zero_mul, add_zero] at ht
      linear_combination ht)
    subst b1
    exact all_even_impossible a0 c0 a1 c1 a2 c2 (by simpa using h)
  obtain ⟨_, h1, _, h3, _, h5, _, _, _, h9, _⟩ :=
    coefficient_equations a0 0 c0 a1 b1 c1 a2 b2 c2 (by simpa using h)
  norm_num [f1, f3, f5, f9] at h1 h3 h5 h9
  have hp := QuinticTwoQuadraticParity.coefficient_classification a1 b1 c1 a2 b2 c2 hb1 hb2
    (by linear_combination h1/5)
    (by linear_combination h3/5)
    (by linear_combination h5)
    (by linear_combination h9/5)
  rcases hp with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · subst a2
    subst b2
    subst c2
    apply QuinticJointReflectedAbsorption.no_reflected_joint_identity a1 b1 c1 a0 c0
    intro t
    have ht := h t
    simp only [neg_mul, sub_eq_add_neg] at ht ⊢
    linear_combination ht
  · subst a2
    subst b2
    subst c2
    apply no_fifth_six c0
    have ht := h 0
    norm_num at ht
    linear_combination ht

/-- Neither reflection nor an arbitrary choice of three rational quadratics
can absorb the two displayed weighted fifth powers. -/
theorem no_joint_identity (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℚ) :
    ¬ (∀ t : ℚ, (a0*t^2+b0*t+c0)^5+(a1*t^2+b1*t+c1)^5+(a2*t^2+b2*t+c2)^5 =
      6*(1-2*t^2)^5+8*(2*t^2)^5) := by
  intro h
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ :=
    coefficient_equations a0 b0 c0 a1 b1 c1 a2 b2 c2 h
  have hb := QuinticJointGeneralCertificate.one_linear_coefficient_zero
    a0 b0 c0 a1 b1 c1 a2 b2 c2 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rcases hb with hb | hb | hb
  · subst b0
    exact even_first_impossible a0 c0 a1 b1 c1 a2 b2 c2 (by simpa using h)
  · subst b1
    apply even_first_impossible a1 c1 a0 b0 c0 a2 b2 c2
    intro t
    have ht := h t
    simp only [zero_mul, add_zero] at ht
    linear_combination ht
  · subst b2
    apply even_first_impossible a2 c2 a0 b0 c0 a1 b1 c1
    intro t
    have ht := h t
    simp only [zero_mul, add_zero] at ht
    linear_combination ht

end Erdos322Research.QuinticJointGeneralAbsorption
