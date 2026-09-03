import FormalConjecturesUtil

/-! A strict sign certificate arising in the paired-linear-coefficient
quintic quadratic ansatz. This is not an unrestricted representation bound. -/
namespace Erdos322Research.QuinticPairedMomentCertificate

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- The residual numerator after eliminating the two odd moment constraints
in a nonsingular normalized paired-linear chart. -/
def residual (c t : ℝ) : ℝ :=
  -3*c^8*t^12 - 12*c^7*t^8 - 12*c^6*t^4 + 16*c^5*t^10 - 4*c^5 +
    30*c^4*t^6 - 4*c^3*t^12 + 16*c^3*t^2 - 12*c^2*t^8 - 12*c*t^4 - 3

/-- Sixteen times the required even-moment equation in normalized coordinates. -/
def evenResidual (b c d t : ℝ) : ℝ :=
  (1+10*b^2+5*b^4+c^5+10*c^3*d^2+5*c*d^4)*(1+c*t^4)-
    4*(1+3*b^2+t^2*(c^3+3*c*d^2))^2


private def A (x : ℝ) : ℝ := x^5*(3*x^3+12*x^2+12*x+4)
private def B (x : ℝ) : ℝ := 4*x^3+12*x^2+12*x+3
private def T (x : ℝ) : ℝ := (8*x^2+15*x+8)*x^3
private def F (x y : ℝ) : ℝ := B x*y^2-2*T x*y+A x

private theorem certificate (x y : ℝ) :
    B x * F x y = (B x*y-T x)^2 +
      4*x^5*(x-1)^2*(x+1)^2*(3*x^2+5*x+3) := by
  unfold F A B T
  ring

private theorem substitution (c t : ℝ) :
    F (c*t^4) (t^10) = -(t^20)*residual c t := by
  unfold F A B T residual
  ring

private theorem F_pos {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) (y : ℝ) :
    0 < F x y := by
  have hB : 0 < B x := by unfold B; positivity
  have hsq : 0 < (x-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hp : 0 < 4*x^5*(x-1)^2*(x+1)^2*(3*x^2+5*x+3) := by positivity
  have he := certificate x y
  have hprod : 0 < B x * F x y := by nlinarith [sq_nonneg (B x*y-T x)]
  exact (mul_pos_iff_of_pos_left hB).mp hprod

/-- The residual cannot vanish in the nonsingular positive-centre chart. -/
theorem residual_neg {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0)
    (hne : c*t^4 ≠ 1) : residual c t < 0 := by
  have ht4 : 0 < t^4 := pow_pos (a := t^2) (sq_pos_of_ne_zero ht) 2 |>.trans_eq (by ring)
  have hF := F_pos (mul_pos hc ht4) hne (t^10)
  rw [substitution] at hF
  have ht20 : 0 < t^20 := by positivity
  by_contra h
  have hn : 0 ≤ residual c t := le_of_not_gt h
  have hnp : -(t^20)*residual c t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hn
  exact (not_lt_of_ge hnp) hF

private theorem elimination (b c d t : ℝ)
    (h₁ : b^2-c^2*d^2*t^6 = 0)
    (h₂ : c^2+d^2-t^2*(1+b^2) = 0)
    (hE : evenResidual b c d t = 0) :
    (c*t^4+1)^2*residual c t = 0 := by
  let K := 1-c^2*t^8
  let R := c^2*t^6*(t^2-c^2)
  let Q₁ := -c*(31*b^2*c*t^6+67*b^2*t^2-17*c^3*t^4-5*c^2+
    31*c*d^2*t^4+31*c*t^6-5*d^2+19*t^2)
  let Q₂ := -31*(c*t^4+1)^2*(K*b^2+R)-
    2*K*(c*t^4+1)*(-24*c^3*t^2+31*c*t^4+7)
  unfold evenResidual at hE
  unfold residual
  linear_combination (norm := (simp only [K,R,Q₁,Q₂]; ring_nf))
    K^2*hE-Q₂*h₁-(K^2*Q₁+c^2*t^6*Q₂)*h₂

/-- The normalized non-paired-centre branch is impossible over the reals,
including its singular denominator chart. -/
theorem normalized_even_moment_impossible {b c d t : ℝ} (hc : 0 < c) (ht : t ≠ 0)
    (h₁ : b^2-c^2*d^2*t^6 = 0)
    (h₂ : c^2+d^2-t^2*(1+b^2) = 0)
    (hE : evenResidual b c d t = 0) : False := by
  by_cases hx : c*t^4 = 1
  · have hK : 1-c^2*t^8 = 0 := by nlinarith [sq_nonneg (c*t^4-1)]
    have hR : c^2*t^6*(t^2-c^2) = 0 := by
      linear_combination b^2*hK-h₁-c^2*t^6*h₂
    have ht6 : t^6 ≠ 0 := pow_ne_zero _ ht
    have htc : t^2 = c^2 := sub_eq_zero.mp
      ((mul_eq_zero.mp hR).resolve_left (mul_ne_zero (pow_ne_zero _ hc.ne') ht6))
    have hc5 : c^5 = 1 := by
      calc
        c^5 = c*(t^2)^2 := by rw [htc]; ring
        _ = c*t^4 := by ring
        _ = 1 := hx
    have hc1 : c = 1 := by
      exact (pow_left_inj₀ hc.le (by norm_num : (0 : ℝ) ≤ 1) (by decide : 5 ≠ 0)).mp
        (by simpa using hc5)
    subst c
    have ht2 : t^2 = 1 := by simpa using htc
    have hd2 : d^2 = b^2 := by nlinarith
    rcases eq_or_eq_neg_of_sq_eq_sq t 1 (by simpa using ht2) with h | h <;>
      rcases eq_or_eq_neg_of_sq_eq_sq d b hd2 with h' | h' <;>
      subst t <;> subst d <;> norm_num [evenResidual] at hE <;>
      nlinarith [sq_nonneg b, sq_nonneg (b^2)]
  · have he := elimination b c d t h₁ h₂ hE
    have hn := residual_neg hc ht hx
    have hp : 0 < (c*t^4+1)^2 := by positivity
    have hneg : (c*t^4+1)^2*residual c t < 0 := mul_neg_of_pos_of_neg hp hn
    linarith

end
end Erdos322Research.QuinticPairedMomentCertificate
