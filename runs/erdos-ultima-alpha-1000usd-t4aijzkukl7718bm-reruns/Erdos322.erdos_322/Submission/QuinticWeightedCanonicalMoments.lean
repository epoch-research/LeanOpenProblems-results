import FormalConjecturesUtil

/-! Exact moments of a normalized weighted-affine quintic construction.
This is not a representation-count bound. -/
namespace Erdos322Research.QuinticWeightedCanonicalMoments
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def p0 (V w : ℚ) : ℚ :=
  (1/40000)+
    (98149/12500000000)*w^1+
    (209/781250000)*w^2+
    (-3677/25000000000)*w^3+
    (-929/50000000000)*w^4+
    (-131/200000000000)*w^5+
    (33/2500)*V^1+
    (49633/6250000)*V^1*w^1+
    (1843/1562500)*V^1*w^2+
    (-159/6250000)*V^1*w^3+
    (-79/5000000)*V^1*w^4+
    (-81/100000000)*V^1*w^5+
    (13503/6250)*V^2+
    (41623/25000)*V^2*w^1+
    (2179/6250)*V^2*w^2+
    (-423/50000)*V^2*w^3+
    (-743/100000)*V^2*w^4+
    (-37/80000)*V^2*w^5+
    132*V^3+
    (2137/25)*V^3*w^1+
    (-24/5)*V^3*w^2+
    (-353/25)*V^3*w^3+
    (-327/100)*V^3*w^4+
    (-81/400)*V^3*w^5+
    2500*V^4+
    (-855)*V^4*w^1+
    (-3640)*V^4*w^2+
    (-4265/2)*V^4*w^3+
    (-1965/4)*V^4*w^4+
    (-655/16)*V^4*w^5

def p1 (V w : ℚ) : ℚ :=
  (-26851/62500000000)+
    (-7703/31250000000)*w^1+
    (-6177/125000000000)*w^2+
    (-527/125000000000)*w^3+
    (-131/1000000000000)*w^4+
    (8133/31250000)*V^1+
    (-5953/31250000)*V^1*w^1+
    (-4861/62500000)*V^1*w^2+
    (-807/125000000)*V^1*w^3+
    (97/500000000)*V^1*w^4+
    (7/250000000)*V^1*w^5+
    (5223/125000)*V^2+
    (-1811/31250)*V^2*w^1+
    (-12049/250000)*V^2*w^2+
    (-1077/125000)*V^2*w^3+
    (-869/2000000)*V^2*w^4+
    (1/500000)*V^2*w^5+
    (-843/125)*V^3+
    (-363/25)*V^3*w^1+
    (-2027/250)*V^3*w^2+
    (-833/500)*V^3*w^3+
    (-171/2000)*V^3*w^4+
    (1/1000)*V^3*w^5+
    (-771)*V^4+
    (-1178)*V^4*w^1+
    (-989/2)*V^4*w^2+
    (-45/2)*V^4*w^3+
    (373/16)*V^4*w^4+
    (7/2)*V^4*w^5

def p2 (V w : ℚ) : ℚ :=
  (-9/100000)+
    (-1543/62500000)*w^1+
    (51/250000000)*w^2+
    (57/125000000)*w^3+
    (7/250000000)*w^4+
    (-723/25000)*V^1+
    (-3463/125000)*V^1*w^1+
    (-447/100000)*V^1*w^2+
    (-21/250000)*V^1*w^3+
    (1/250000)*V^1*w^4+
    (-1/1000000)*V^1*w^5+
    (-723/250)*V^2+
    (-641/250)*V^2*w^1+
    (-547/1000)*V^2*w^2+
    (39/500)*V^2*w^3+
    (19/1000)*V^2*w^4+
    (1/1000)*V^2*w^5+
    (-90)*V^3+
    62*V^3*w^1+
    (219/2)*V^3*w^2+
    33*V^3*w^3+
    2*V^3*w^4+
    (-1/4)*V^3*w^5

def p3 (V w : ℚ) : ℚ :=
  (207/125000000)+
    (97/62500000)*w^1+
    (139/500000000)*w^2+
    (7/500000000)*w^3+
    (-2013/250000)*V^1+
    (-1/5000)*V^1*w^1+
    (283/1000000)*V^1*w^2+
    (-3/1000000)*V^1*w^3+
    (-3/1000000)*V^1*w^4+
    (-231/500)*V^2+
    (13/250)*V^2*w^1+
    (569/2000)*V^2*w^2+
    (21/400)*V^2*w^3+
    (3/1000)*V^2*w^4+
    69*V^3+
    78*V^3*w^1+
    (49/4)*V^3*w^2+
    (-13/4)*V^3*w^3+
    (-3/4)*V^3*w^4

def p4 (V w : ℚ) : ℚ :=
  (21/12500)+
    (101/250000)*w^1+
    (-7/250000)*w^2+
    (-3/500000)*w^3+
    (6/25)*V^1+
    (131/250)*V^1*w^1+
    (1/10)*V^1*w^2+
    (3/500)*V^1*w^3+
    (84/5)*V^2+
    (-19)*V^2*w^1+
    (-11)*V^2*w^2+
    (-3/2)*V^2*w^3

def p5 (V w : ℚ) : ℚ :=
  (3/50000)+
    (-1/12500)*w^1+
    (-1/100000)*w^2+
    (39/50)*V^1+
    (4/25)*V^1*w^1+
    (1/100)*V^1*w^2+
    (-45)*V^2+
    (-20)*V^2*w^1+
    (-5/2)*V^2*w^2

def constX (v w : ℚ) : ℚ := -(1000*v^2+500*v^2*w+10+w)/200
def constY (v w : ℚ) : ℚ := -(1500*v^2+500*v^2*w+9+w)/250

def remainder (v w t : ℚ) : ℚ :=
  let P := -v*(w+4)/5-t/5
  let A := t^2+v*(w-1)*t+constX v w
  let Y := t^2+v*w*t+constY v w
  t*((P/2+A)^5+(P/2-A)^5)+Y^5-(constY v w)^5

theorem remainder_expansion (v w t : ℚ) :
    remainder v w t = -t*(v*p0 (v^2) w+5*p1 (v^2) w*t+
      10*v*p2 (v^2) w*t^2+10*p3 (v^2) w*t^3+
      5*v*p4 (v^2) w*t^4+p5 (v^2) w*t^5) := by
  dsimp [remainder, constX, constY, p0, p1, p2, p3, p4, p5]
  ring

private def affineFifth (a b : ℚ) : ℚ[X] := (C b*X+C a)^5
private theorem affineFifth_coeff (a b : ℚ) (j : ℕ) :
    (affineFifth a b).coeff j = (Nat.choose 5 j : ℚ)*(a^(5-j)*b^j) := by
  have he : affineFifth a b = ((X+C a)^5).comp (C b*X) := by simp [affineFifth]
  rw [he, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  ring

private def targetPolynomial (v w : ℚ) : ℚ[X] :=
  C (v*p0 (v^2) w)+C (5*p1 (v^2) w)*X+C (10*v*p2 (v^2) w)*X^2+
    C (10*p3 (v^2) w)*X^3+C (5*v*p4 (v^2) w)*X^4+C (p5 (v^2) w)*X^5

theorem necessary_moments (v w a b c d : ℚ)
    (h : ∀ t : ℚ, remainder v w t+t*((a+b*t)^5+(c+d*t)^5) = 0) :
    a^5+c^5 = v*p0 (v^2) w ∧
    a^4*b+c^4*d = p1 (v^2) w ∧
    a^3*b^2+c^3*d^2 = v*p2 (v^2) w ∧
    a^2*b^3+c^2*d^3 = p3 (v^2) w ∧
    a*b^4+c*d^4 = v*p4 (v^2) w ∧
    b^5+d^5 = p5 (v^2) w := by
  have hm : X*(affineFifth a b+affineFifth c d-targetPolynomial v w) = 0 := by
    apply Polynomial.funext
    intro t
    simp only [affineFifth, targetPolynomial, eval_add, eval_sub, eval_mul, eval_pow,
      eval_C, eval_X, eval_zero]
    have ht := h t
    rw [remainder_expansion] at ht
    linear_combination ht
  have hp : affineFifth a b+affineFifth c d = targetPolynomial v w :=
    sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left Polynomial.X_ne_zero)
  have hc (j : ℕ) : (affineFifth a b).coeff j+(affineFifth c d).coeff j =
      (targetPolynomial v w).coeff j := by
    have he := congrArg (fun P : ℚ[X] => P.coeff j) hp
    simpa only [coeff_add] using he
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  norm_num [affineFifth_coeff, targetPolynomial, coeff_C_mul, coeff_X_pow,
    coeff_X, coeff_C, Nat.choose, mul_assoc] at h0 h1 h2 h3 h4 h5
  exact ⟨h0, by linarith, by linarith, by linarith, by linarith, h5⟩

def minor0 (m0 m1 m2 m3 m4 : ℚ) : ℚ :=
  m0*m2*m4-m0*m3^2-m1^2*m4+2*m1*m2*m3-m2^3

def minor3 (m1 m2 m3 m4 m5 : ℚ) : ℚ :=
  m1*m3*m5-m1*m4^2-m2^2*m5+2*m2*m3*m4-m3^3

theorem two_affine_minor0 (a b c d : ℚ) :
    minor0 (a^5+c^5) (a^4*b+c^4*d) (a^3*b^2+c^3*d^2)
      (a^2*b^3+c^2*d^3) (a*b^4+c*d^4) = 0 := by
  unfold minor0
  ring

theorem two_affine_minor3 (a b c d : ℚ) :
    minor3 (a^4*b+c^4*d) (a^3*b^2+c^3*d^2) (a^2*b^3+c^2*d^3)
      (a*b^4+c*d^4) (b^5+d^5) = 0 := by
  unfold minor3
  ring

end
end Erdos322Research.QuinticWeightedCanonicalMoments
