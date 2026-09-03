import FormalConjecturesUtil

/-! A classification of one normalized degree-five reflection chart for five
fifth powers. This is an obstruction to a restricted polynomial construction,
not an unrestricted representation-count bound or a settlement of Erdős 322. -/
namespace Erdos322Research.QuinticLowLast
noncomputable section
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 2048

private def pair (p q : ℝ[X]) : ℝ[X] :=
  10*X^2*p^4*q+20*X*p^2*q^3+2*q^5

def core (a b c d y : ℝ) : ℝ[X] :=
  pair (X^2+C a*X+C (b+y)) (X^2+C c*X+C (d-4*y)) -
  pair (X^2+C a*X+C (b-y)) (X^2+C c*X+C (d+4*y))

private def q0 (a b c d y : ℝ) : ℝ :=
  -5 * d ^ 4 - 160 * d ^ 2 * y ^ 2 - 256 * y ^ 4

private def q1 (a b c d y : ℝ) : ℝ :=
  -30 * b ^ 2 * d ^ 2 + 5 * b * d ^ 3 - 20 * c * d ^ 3 - 160 * b ^ 2 * y ^ 2 + 240 * b * d * y ^ 2 - 320 * c * d * y ^ 2 - 30 * d ^ 2 * y ^ 2 - 160 * y ^ 4

private def q2 (a b c d y : ℝ) : ℝ :=
  -5 * b ^ 4 + 5 * b ^ 3 * d - 60 * b ^ 2 * c * d - 60 * a * b * d ^ 2 + 15 * b * c * d ^ 2 - 30 * c ^ 2 * d ^ 2 + 5 * a * d ^ 3 - 320 * a * b * y ^ 2 - 30 * b ^ 2 * y ^ 2 + 240 * b * c * y ^ 2 - 160 * c ^ 2 * y ^ 2 + 240 * a * d * y ^ 2 + 5 * b * d * y ^ 2 - 60 * c * d * y ^ 2 - 5 * y ^ 4 - 20 * d ^ 3 - 320 * d * y ^ 2

private def q3 (a b c d y : ℝ) : ℝ :=
  -20 * a * b ^ 3 + 5 * b ^ 3 * c - 30 * b ^ 2 * c ^ 2 + 15 * a * b ^ 2 * d - 120 * a * b * c * d + 15 * b * c ^ 2 * d - 20 * c ^ 3 * d - 30 * a ^ 2 * d ^ 2 + 15 * a * c * d ^ 2 - 160 * a ^ 2 * y ^ 2 - 60 * a * b * y ^ 2 + 240 * a * c * y ^ 2 + 5 * b * c * y ^ 2 - 30 * c ^ 2 * y ^ 2 + 5 * a * d * y ^ 2 - 60 * b ^ 2 * d - 45 * b * d ^ 2 - 60 * c * d ^ 2 + 5 * d ^ 3 - 80 * b * y ^ 2 - 320 * c * y ^ 2 + 180 * d * y ^ 2

private def q4 (a b c d y : ℝ) : ℝ :=
  -30 * a ^ 2 * b ^ 2 + 15 * a * b ^ 2 * c - 60 * a * b * c ^ 2 + 5 * b * c ^ 3 - 5 * c ^ 4 + 15 * a ^ 2 * b * d - 60 * a ^ 2 * c * d + 15 * a * c ^ 2 * d - 30 * a ^ 2 * y ^ 2 + 5 * a * c * y ^ 2 - 15 * b ^ 3 - 60 * b ^ 2 * c - 120 * a * b * d + 15 * b ^ 2 * d - 90 * b * c * d - 60 * c ^ 2 * d - 45 * a * d ^ 2 + 15 * c * d ^ 2 - 80 * a * y ^ 2 - 55 * b * y ^ 2 + 180 * c * y ^ 2 + 5 * d * y ^ 2 - 30 * d ^ 2 - 160 * y ^ 2

private def q5 (a b c d y : ℝ) : ℝ :=
  -20 * a ^ 3 * b + 15 * a ^ 2 * b * c - 30 * a ^ 2 * c ^ 2 + 5 * a * c ^ 3 + 5 * a ^ 3 * d - 45 * a * b ^ 2 - 120 * a * b * c + 15 * b ^ 2 * c - 45 * b * c ^ 2 - 20 * c ^ 3 - 60 * a ^ 2 * d + 30 * a * b * d - 90 * a * c * d + 15 * c ^ 2 * d - 55 * a * y ^ 2 + 5 * c * y ^ 2 - 30 * b ^ 2 - 105 * b * d - 60 * c * d - 15 * d ^ 2 + 50 * y ^ 2

private def q6 (a b c d y : ℝ) : ℝ :=
  -5 * a ^ 4 + 5 * a ^ 3 * c - 45 * a ^ 2 * b - 60 * a ^ 2 * c + 30 * a * b * c - 45 * a * c ^ 2 + 5 * c ^ 3 + 15 * a ^ 2 * d - 60 * a * b - 15 * b ^ 2 - 105 * b * c - 30 * c ^ 2 - 105 * a * d + 15 * b * d - 30 * c * d - 25 * y ^ 2 - 20 * d

private def q7 (a b c d y : ℝ) : ℝ :=
  -15 * a ^ 3 + 15 * a ^ 2 * c - 30 * a ^ 2 - 30 * a * b - 105 * a * c + 15 * b * c - 15 * c ^ 2 + 15 * a * d - 55 * b - 20 * c - 45 * d

private def q8 (a b c d y : ℝ) : ℝ :=
  -15 * a ^ 2 + 15 * a * c - 55 * a - 5 * b - 45 * c + 5 * d - 5

private def q9 (a b c d y : ℝ) : ℝ :=
  -5 * a + 5 * c - 25

private lemma core_expansion (a b c d y : ℝ) :
  core a b c d y = C (16*y) * (
    C (q0 a b c d y) +
    C (q1 a b c d y) * X^1 +
    C (q2 a b c d y) * X^2 +
    C (q3 a b c d y) * X^3 +
    C (q4 a b c d y) * X^4 +
    C (q5 a b c d y) * X^5 +
    C (q6 a b c d y) * X^6 +
    C (q7 a b c d y) * X^7 +
    C (q8 a b c d y) * X^8 +
    C (q9 a b c d y) * X^9 ) := by
  simp only [core, pair, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
  ring

private lemma core_coefficients (a b c d y : ℝ) :
    (core a b c d y).coeff 9 = 16*y*q9 a b c d y ∧
    (core a b c d y).coeff 8 = 16*y*q8 a b c d y ∧
    (core a b c d y).coeff 7 = 16*y*q7 a b c d y ∧
    (core a b c d y).coeff 6 = 16*y*q6 a b c d y ∧
    (core a b c d y).coeff 5 = 16*y*q5 a b c d y ∧
    (core a b c d y).coeff 4 = 16*y*q4 a b c d y ∧
    (core a b c d y).coeff 3 = 16*y*q3 a b c d y := by
  rw [core_expansion]
  simp only [coeff_C_mul, coeff_add, coeff_X_pow, coeff_X, coeff_C]
  norm_num

private lemma last_coefficients (v w : ℝ) :
    ((C v*X+C w)^5 : ℝ[X]).coeff 9 = 0 ∧
    ((C v*X+C w)^5 : ℝ[X]).coeff 8 = 0 ∧
    ((C v*X+C w)^5 : ℝ[X]).coeff 7 = 0 ∧
    ((C v*X+C w)^5 : ℝ[X]).coeff 6 = 0 ∧
    ((C v*X+C w)^5 : ℝ[X]).coeff 5 = v^5 ∧
    ((C v*X+C w)^5 : ℝ[X]).coeff 4 = 5*v^4*w ∧
    ((C v*X+C w)^5 : ℝ[X]).coeff 3 = 10*v^3*w^2 := by
  have he : ((C v*X+C w)^5 : ℝ[X]) =
      C (v^5)*X^5+C (5*v^4*w)*X^4+C (10*v^3*w^2)*X^3+
      C (10*v^2*w^3)*X^2+C (5*v*w^4)*X+C (w^5) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [he]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

private def positivePolynomial (u : ℝ) : ℝ :=
  29296875 * u ^ 6 + 7753281250 * u ^ 5 + 1721443295000 * u ^ 4 + 258562440021600 * u ^ 3 + 24390550324867727 * u ^ 2 + 1077464875856298358 * u + 22526133164627553318

private def aVal (y : ℝ) : ℝ := -(25*y^2+7436)/429
private def bVal (y : ℝ) : ℝ := -(46*aVal y+509)/5
private def cVal (y : ℝ) : ℝ := aVal y+5
private def dVal (y : ℝ) : ℝ := bVal y+5*aVal y+46

private lemma invariant_identity (y : ℝ) :
    5*q5 (aVal y) (bVal y) (cVal y) (dVal y) y *
      q3 (aVal y) (bVal y) (cVal y) (dVal y) y -
    2*(q4 (aVal y) (bVal y) (cVal y) (dVal y) y)^2 =
    -(25/33871089681 : ℝ)*positivePolynomial (y^2) := by
  simp only [q5,q3,q4,aVal,bVal,cVal,dVal,positivePolynomial]
  ring

private lemma positivePolynomial_pos (u : ℝ) (hu : 0 ≤ u) :
    0 < positivePolynomial u := by
  unfold positivePolynomial
  positivity

/-- In this chart every constant fifth-power sum consists only of cancelling
pairs and a constant last coordinate. -/
theorem normalized_polynomial_classification (a b c d y v w N : ℝ)
    (he : core a b c d y + (C v*X+C w)^5 = C N) :
    y=0 ∧ v=0 ∧ N=w^5 := by
  obtain ⟨h9,h8,h7,h6,h5,h4,h3⟩ := core_coefficients a b c d y
  obtain ⟨l9,l8,l7,l6,l5,l4,l3⟩ := last_coefficients v w
  have e9 := congrArg (fun p : ℝ[X] ↦ p.coeff 9) he
  have e8 := congrArg (fun p : ℝ[X] ↦ p.coeff 8) he
  have e7 := congrArg (fun p : ℝ[X] ↦ p.coeff 7) he
  have e6 := congrArg (fun p : ℝ[X] ↦ p.coeff 6) he
  have e5 := congrArg (fun p : ℝ[X] ↦ p.coeff 5) he
  have e4 := congrArg (fun p : ℝ[X] ↦ p.coeff 4) he
  have e3 := congrArg (fun p : ℝ[X] ↦ p.coeff 3) he
  simp only [coeff_add, h9, l9, coeff_C, OfNat.ofNat_ne_zero, if_false, add_zero] at e9
  simp only [coeff_add, h8, l8, coeff_C, OfNat.ofNat_ne_zero, if_false, add_zero] at e8
  simp only [coeff_add, h7, l7, coeff_C, OfNat.ofNat_ne_zero, if_false, add_zero] at e7
  simp only [coeff_add, h6, l6, coeff_C, OfNat.ofNat_ne_zero, if_false, add_zero] at e6
  simp only [coeff_add, h5, l5, coeff_C, OfNat.ofNat_ne_zero, if_false] at e5
  simp only [coeff_add, h4, l4, coeff_C, OfNat.ofNat_ne_zero, if_false] at e4
  simp only [coeff_add, h3, l3, coeff_C, OfNat.ofNat_ne_zero, if_false] at e3
  have hy : y=0 := by
    by_contra hy
    have hfac : 16*y ≠ 0 := mul_ne_zero (by norm_num) hy
    have z9 := (mul_eq_zero.mp e9).resolve_left hfac
    have z8 := (mul_eq_zero.mp e8).resolve_left hfac
    have z7 := (mul_eq_zero.mp e7).resolve_left hfac
    have z6 := (mul_eq_zero.mp e6).resolve_left hfac
    have hc : c=a+5 := by dsimp [q9] at z9; linarith
    have hd : d=b+5*a+46 := by rw [hc] at z8; dsimp [q8] at z8; nlinarith only [z8]
    have hb : b=-(46*a+509)/5 := by
      rw [hc,hd] at z7
      dsimp [q7] at z7
      nlinarith only [z7]
    have ha : a=aVal y := by
      rw [hc,hd,hb] at z6
      dsimp [q6] at z6
      dsimp [aVal]
      nlinarith only [z6]
    have hb' : b=bVal y := by rw [hb,ha]; rfl
    have hc' : c=cVal y := by rw [hc,ha]; rfl
    have hd' : d=dVal y := by rw [hd,ha,hb']; rfl
    have inv : 5*q5 a b c d y*q3 a b c d y - 2*(q4 a b c d y)^2 = 0 := by
      have e5' : 16*y*q5 a b c d y = -v^5 := by linarith only [e5]
      have e4' : 16*y*q4 a b c d y = -(5*v^4*w) := by linarith only [e4]
      have e3' : 16*y*q3 a b c d y = -(10*v^3*w^2) := by linarith only [e3]
      have hm : (16*y)^2*(5*q5 a b c d y*q3 a b c d y - 2*(q4 a b c d y)^2)=0 := by
        calc
          _ = 5*(16*y*q5 a b c d y)*(16*y*q3 a b c d y) -
              2*(16*y*q4 a b c d y)^2 := by ring
          _ = 0 := by rw [e5',e3',e4']; ring
      exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hfac)
    rw [ha,hb',hc',hd',invariant_identity] at inv
    have hp := positivePolynomial_pos (y^2) (sq_nonneg y)
    have hn : -(25/33871089681 : ℝ)*positivePolynomial (y^2) < 0 := by
      exact mul_neg_of_neg_of_pos (by norm_num) hp
    exact (ne_of_lt hn) inv
  subst y
  have hc0 : core a b c d 0 = 0 := by simp [core]
  rw [hc0,zero_add] at he
  have ev := congrArg (fun p : ℝ[X] ↦ p.coeff 5) he
  simp only [l5, coeff_C, OfNat.ofNat_ne_zero, if_false] at ev
  norm_num at ev
  have hv : v=0 := ev
  subst v
  simp only [map_zero,zero_mul,zero_add,← map_pow] at he
  exact ⟨rfl,rfl,(Polynomial.C_injective he).symm⟩

/-- The five coordinates of the normalized equal-leading, equal-cubic-term
chart. The last coordinate has degree at most two. -/
def coordinates (a b c d y v w t : ℝ) : Fin 5 → ℝ :=
  let p := t^5+a*t^3+b*t
  let q := t^4+c*t^2+d
  ![p+y*t+q-4*y, -p-y*t+q-4*y, p-y*t-q-4*y,
    -p+y*t-q-4*y, v*t^2+w]

private lemma sum_expansion (a b c d y v w t : ℝ) :
    ∑ i, coordinates a b c d y v w t i ^ 5 =
      (core a b c d y + (C v*X+C w)^5).eval (t^2) := by
  simp [coordinates, Fin.sum_univ_succ, core, pair]
  ring

/-- A constant sum throughout this polynomial chart has only cancelling
pairs. This is not a classification of general quintic representations. -/
theorem constant_sum_classification (a b c d y v w N : ℝ)
    (he : ∀ t : ℝ, ∑ i, coordinates a b c d y v w t i ^ 5 = N) :
    y=0 ∧ v=0 ∧ N=w^5 := by
  apply normalized_polynomial_classification
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro u hu
  change (core a b c d y + (C v*X+C w)^5).eval u = (C N).eval u
  have hs := he (Real.sqrt u)
  rw [sum_expansion, Real.sq_sqrt hu] at hs
  simpa using hs

/-- No member of this constant-sum chart passes through an all-positive point. -/
theorem no_positive_constant_sum (a b c d y v w N t : ℝ)
    (he : ∀ s : ℝ, ∑ i, coordinates a b c d y v w s i ^ 5 = N) :
    ¬ ∀ i, 0 < coordinates a b c d y v w t i := by
  obtain ⟨hy,_,_⟩ := constant_sum_classification a b c d y v w N he
  intro hp
  have h0 := hp 0
  have h3 := hp 3
  simp [coordinates,hy] at h0 h3
  linarith


end
end Erdos322Research.QuinticLowLast
