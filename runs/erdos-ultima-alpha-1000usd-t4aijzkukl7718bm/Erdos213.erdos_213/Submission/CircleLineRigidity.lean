import Submission.DescartesReflection
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Polynomial rigidity for a circle-inversion experiment. These results concern
identities along a line of inversion poles, not arbitrary rational-distance sets. -/
namespace Erdos213.CircleLineRigidity
open Polynomial

noncomputable def quad {K : Type*} [Semiring K] (a b c : K) : K[X] :=
  C a * X^2 + C b * X + C c

lemma quad_coeff_two {K : Type*} [Semiring K] (a b c : K) :
    (quad a b c).coeff 2 = a := by simp [quad]
lemma quad_coeff_one {K : Type*} [Semiring K] (a b c : K) :
    (quad a b c).coeff 1 = b := by simp [quad]
lemma quad_coeff_zero {K : Type*} [Semiring K] (a b c : K) :
    (quad a b c).coeff 0 = c := by simp [quad]

lemma quad_ne_zero {K : Type*} [Semiring K] {a b c : K} (ha : a ≠ 0) :
    quad a b c ≠ 0 := by
  intro h
  have := congrArg (fun p : K[X] => p.coeff 2) h
  apply ha
  simpa [quad_coeff_two] using this

lemma quad_natDegree {K : Type*} [Semiring K] [Nontrivial K] {a b c : K}
    (ha : a ≠ 0) : (quad a b c).natDegree = 2 := by
  unfold quad
  compute_degree!

lemma quad_map {K L : Type*} [Semiring K] [Semiring L] (f : K →+* L) (a b c : K) :
    (quad a b c).map f = quad (f a) (f b) (f c) := by simp [quad]

lemma quad_complex_split (a b c : ℂ) :
    quad a b c = quad (a.re : ℂ) (b.re : ℂ) (c.re : ℂ) +
      C Complex.I * quad (a.im : ℂ) (b.im : ℂ) (c.im : ℂ) := by
  calc
    _ = quad ((a.re : ℂ)+a.im*Complex.I) ((b.re : ℂ)+b.im*Complex.I)
        ((c.re : ℂ)+c.im*Complex.I) := by rw [Complex.re_add_im, Complex.re_add_im, Complex.re_add_im]
    _ = _ := by simp only [quad, C_add, C_mul]; ring

lemma quad_conjugate_product (a b c : ℂ) :
    quad a b c * quad ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ((starRingEnd ℂ) c) =
      ((quad a.re b.re c.re)^2 + (quad a.im b.im c.im)^2).map (algebraMap ℝ ℂ) := by
  have hi : (C Complex.I : ℂ[X])^2 = -1 := by
    rw [← C_pow, Complex.I_sq, C_neg, C_1]
  have hc : quad ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ((starRingEnd ℂ) c) =
      quad (a.re : ℂ) (b.re : ℂ) (c.re : ℂ) -
        C Complex.I * quad (a.im : ℂ) (b.im : ℂ) (c.im : ℂ) := by
    rw [quad_complex_split]
    simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg]
    simp [quad, map_neg]
    ring
  rw [hc, quad_complex_split a b c, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_pow, quad_map, quad_map]
  change (_ + C Complex.I * _) * (_ - C Complex.I * _) = _
  calc
    _ = (quad (a.re : ℂ) (b.re : ℂ) (c.re : ℂ))^2 -
        (C Complex.I)^2 * (quad (a.im : ℂ) (b.im : ℂ) (c.im : ℂ))^2 := by ring
    _ = _ := by rw [hi]; simp only [Complex.coe_algebraMap]; ring

lemma quad_separable {K : Type*} [Field K] (a b c : K)
    (hd : b^2-4*a*c ≠ 0) : (quad a b c).Separable := by
  let d := b^2-4*a*c
  have h : C (-4*a)*quad a b c + (C (2*a)*X+C b)*(quad a b c).derivative = C d := by
    simp [quad, d, derivative_add, derivative_mul, map_ofNat]
    ring
  apply (separable_def' _).mpr
  refine ⟨C d⁻¹ * C (-4*a), C d⁻¹*(C (2*a)*X+C b), ?_⟩
  calc
    _ = C d⁻¹*(C (-4*a)*quad a b c + (C (2*a)*X+C b)*(quad a b c).derivative) := by ring
    _ = C d⁻¹*C d := by rw [h]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hd, C_1]

lemma squarefree_dvd_partner {K : Type*} [Field K] {f g : K[X]}
    (hf : f ≠ 0) (hsf : Squarefree f) (hsq : IsSquare (f*g)) : f ∣ g := by
  obtain ⟨p,hp⟩ := hsq
  have hd : f ∣ p^2 := ⟨g, by simpa only [pow_two] using hp.symm⟩
  obtain ⟨q,hq⟩ := (hsf.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0)).mp hd
  refine ⟨q^2, ?_⟩
  apply mul_left_cancel₀ hf
  calc
    f*g = p*p := hp
    _ = f*(f*q^2) := by rw [hq]; ring

/-- With nonzero real discriminant, a complex quadratic whose conjugate product
is square must be real or purely imaginary coefficient by coefficient. -/
lemma real_discriminant_square_norm (a b c : ℂ) (ha : a ≠ 0)
    (hd : b^2-4*a*c ≠ 0)
    (hr : (starRingEnd ℂ) (b^2-4*a*c) = b^2-4*a*c)
    (hsq : IsSquare (quad a b c *
      quad ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ((starRingEnd ℂ) c))) :
    (a.im = 0 ∧ b.im = 0 ∧ c.im = 0) ∨
    (a.re = 0 ∧ b.re = 0 ∧ c.re = 0) := by
  let f := quad a b c
  let g := quad ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ((starRingEnd ℂ) c)
  have hf : f ≠ 0 := quad_ne_zero ha
  have ha' : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  have hg : g ≠ 0 := quad_ne_zero ha'
  have hdvd : f ∣ g := squarefree_dvd_partner hf (quad_separable a b c hd).squarefree hsq
  obtain ⟨q,hq⟩ := hdvd
  have hq0 : q ≠ 0 := by intro h; apply hg; simp [hq,h]
  have hdeg := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change g.natDegree = (f*q).natDegree at hdeg
  rw [natDegree_mul hf hq0] at hdeg
  change (quad ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ((starRingEnd ℂ) c)).natDegree =
    (quad a b c).natDegree + q.natDegree at hdeg
  rw [quad_natDegree ha, quad_natDegree ha'] at hdeg
  have hn : q.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hn] at hq
  let z := q.coeff 0
  have he2 := congrArg (fun p : ℂ[X] => p.coeff 2) hq
  have he1 := congrArg (fun p : ℂ[X] => p.coeff 1) hq
  have he0 := congrArg (fun p : ℂ[X] => p.coeff 0) hq
  change (g.coeff 2) = (f*C z).coeff 2 at he2
  change (g.coeff 1) = (f*C z).coeff 1 at he1
  change (g.coeff 0) = (f*C z).coeff 0 at he0
  simp only [f, g, coeff_mul_C, quad_coeff_two, quad_coeff_one, quad_coeff_zero] at he2 he1 he0
  have hz : (1-z^2)*(b^2-4*a*c) = 0 := by
    have hh : b^2-4*a*c = z^2*(b^2-4*a*c) := by
      calc
        _ = (starRingEnd ℂ) (b^2-4*a*c) := hr.symm
        _ = ((starRingEnd ℂ) b)^2-4*((starRingEnd ℂ) a)*((starRingEnd ℂ) c) := by simp [map_ofNat]
        _ = _ := by rw [he2,he1,he0]; ring
    linear_combination hh
  have hz2 : z^2 = 1 := by
    have he := (mul_eq_zero.mp hz).resolve_right hd
    linear_combination -he
  have hp : (z-1)*(z+1) = 0 := by linear_combination hz2
  rcases mul_eq_zero.mp hp with hz1 | hzm
  · have hz1' : z = 1 := sub_eq_zero.mp hz1
    simp only [hz1', mul_one] at he2 he1 he0
    exact Or.inl ⟨Complex.conj_eq_iff_im.mp he2, Complex.conj_eq_iff_im.mp he1,
      Complex.conj_eq_iff_im.mp he0⟩
  · have hzm' : z = -1 := by linear_combination hzm
    simp only [hzm', mul_neg, mul_one] at he2 he1 he0
    have h2 := congrArg Complex.re he2
    have h1 := congrArg Complex.re he1
    have h0 := congrArg Complex.re he0
    simp only [Complex.conj_re, Complex.neg_re] at h2 h1 h0
    exact Or.inr ⟨by linarith, by linarith, by linarith⟩

/-- The quadratic numerator for the difference of two circle centers after
inversion about `(t,0)`, encoded as one complex polynomial. -/
def circleA (x y X Y : ℝ) : ℂ := ⟨X-x,y-Y⟩
def circleB (x y r X Y s : ℝ) : ℂ :=
  ⟨x^2+y^2-r^2-X^2-Y^2+s^2, 2*(x*Y-X*y)⟩
def circleC (x y r X Y s : ℝ) : ℂ :=
  ⟨x*(X^2+Y^2-s^2)-X*(x^2+y^2-r^2),
   y*(X^2+Y^2-s^2)-Y*(x^2+y^2-r^2)⟩

lemma circle_discriminant (x y r X Y s : ℝ) :
    circleB x y r X Y s ^ 2 - 4*circleA x y X Y*circleC x y r X Y s =
      (((x-X)^2+(y-Y)^2-(r+s)^2)*((x-X)^2+(y-Y)^2-(r-s)^2) : ℝ) := by
  apply Complex.ext <;>
    simp [circleA, circleB, circleC, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

private lemma separated_same_power_false (y r Y s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hy : y < -r) (hY : Y < -s)
    (hp : y^2-r^2 = Y^2-s^2) (hd : (r+s)^2 < (y-Y)^2) : False := by
  have hsum : 0 < r+s := by linarith
  have ht : r+s < -y-Y := by linarith
  rcases le_total y Y with hle | hle
  · have hdiff : r+s < Y-y := by nlinarith
    have hm : (r+s)^2 < (Y-y)*(-y-Y) := by
      calc
        (r+s)^2 = (r+s)*(r+s) := by ring
        _ < (Y-y)*(r+s) := mul_lt_mul_of_pos_right hdiff hsum
        _ < (Y-y)*(-y-Y) := mul_lt_mul_of_pos_left ht (by linarith)
    nlinarith [mul_pos hr hs]
  · have hdiff : r+s < y-Y := by nlinarith
    have hm : (r+s)^2 < (y-Y)*(-y-Y) := by
      calc
        (r+s)^2 = (r+s)*(r+s) := by ring
        _ < (y-Y)*(r+s) := mul_lt_mul_of_pos_right hdiff hsum
        _ < (y-Y)*(-y-Y) := mul_lt_mul_of_pos_left ht (by linarith)
    nlinarith [mul_pos hr hs]

/-- Strictly externally separated positive-radius circles lying below the line
of poles cannot have a universally square center-distance numerator. This is
not an obstruction to rational distances at selected individual poles. -/
lemma separated_circles_no_square (x y r X Y s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hy : y < -r) (hY : Y < -s)
    (hsep : (r+s)^2 < (x-X)^2+(y-Y)^2) :
    ¬ IsSquare (quad (circleA x y X Y) (circleB x y r X Y s) (circleC x y r X Y s) *
      quad ((starRingEnd ℂ) (circleA x y X Y))
        ((starRingEnd ℂ) (circleB x y r X Y s))
        ((starRingEnd ℂ) (circleC x y r X Y s))) := by
  intro hsq
  have ha : circleA x y X Y ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [circleA, Complex.zero_re, Complex.zero_im] at hre him
    have hxx : x = X := by linarith
    have hyy : y = Y := by linarith
    subst X Y
    nlinarith [sq_nonneg (r+s)]
  have hpos : 0 < ((x-X)^2+(y-Y)^2-(r+s)^2)*((x-X)^2+(y-Y)^2-(r-s)^2) := by
    apply mul_pos
    · linarith
    · nlinarith [mul_pos hr hs]
  have hd : circleB x y r X Y s^2-4*circleA x y X Y*circleC x y r X Y s ≠ 0 := by
    rw [circle_discriminant]
    exact_mod_cast ne_of_gt hpos
  have hre : (starRingEnd ℂ) (circleB x y r X Y s^2-
      4*circleA x y X Y*circleC x y r X Y s) =
      circleB x y r X Y s^2-4*circleA x y X Y*circleC x y r X Y s := by
    rw [circle_discriminant]
    simp
  rcases real_discriminant_square_norm _ _ _ ha hd hre hsq with hi | he
  · have hyy : y = Y := by simpa [circleA, sub_eq_zero] using hi.1
    have hb : 2*(x*Y-X*y) = 0 := hi.2.1
    have hy0 : y ≠ 0 := by linarith
    have hxx : x = X := by
      subst Y
      have hz : (x-X)*y = 0 := by linear_combination hb/2
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hy0)
    subst X Y
    nlinarith [sq_nonneg (r+s)]
  · have hxx : X = x := by simpa [circleA, sub_eq_zero] using he.1
    have hb : x^2+y^2-r^2-X^2-Y^2+s^2 = 0 := he.2.1
    subst X
    apply separated_same_power_false y r Y s hr hs hy hY
    · nlinarith
    · simpa using hsep

lemma separated_real_numerator_no_square (x y r X Y s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hy : y < -r) (hY : Y < -s)
    (hsep : (r+s)^2 < (x-X)^2+(y-Y)^2) :
    ¬ IsSquare ((quad (circleA x y X Y).re (circleB x y r X Y s).re
        (circleC x y r X Y s).re)^2 +
      (quad (circleA x y X Y).im (circleB x y r X Y s).im
        (circleC x y r X Y s).im)^2) := by
  rintro ⟨p,hp⟩
  apply separated_circles_no_square x y r X Y s hr hs hy hY hsep
  rw [quad_conjugate_product]
  refine ⟨p.map (algebraMap ℝ ℂ), ?_⟩
  rw [hp, Polynomial.map_mul]

lemma polynomial_square_of_ratFunc_square {K : Type*} [Field K] (p : K[X])
    (h : IsSquare (algebraMap K[X] (RatFunc K) p)) : IsSquare p := by
  obtain ⟨r,hr⟩ := h
  have hint : IsIntegral K[X] (r^2) := by
    rw [pow_two, ← hr]
    exact isIntegral_algebraMap
  obtain ⟨q,hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := K[X]) (K := RatFunc K) (by norm_num : 0 < (2 : ℕ)) hint
  refine ⟨q, ?_⟩
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa [map_mul,hq] using hr

lemma separated_ratFunc_numerator_no_square (x y r X Y s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hy : y < -r) (hY : Y < -s)
    (hsep : (r+s)^2 < (x-X)^2+(y-Y)^2) :
    ¬ IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      ((quad (circleA x y X Y).re (circleB x y r X Y s).re (circleC x y r X Y s).re)^2 +
       (quad (circleA x y X Y).im (circleB x y r X Y s).im (circleC x y r X Y s).im)^2)) := by
  intro h
  exact separated_real_numerator_no_square x y r X Y s hr hs hy hY hsep
    (polynomial_square_of_ratFunc_square _ h)

noncomputable def realNumerator (x y r X Y s : ℝ) : ℝ[X] :=
  (quad (circleA x y X Y).re (circleB x y r X Y s).re (circleC x y r X Y s).re)^2 +
  (quad (circleA x y X Y).im (circleB x y r X Y s).im (circleC x y r X Y s).im)^2

noncomputable def powerPolynomial (x y r : ℝ) : ℝ[X] :=
  quad 1 (-2*x) (x^2+y^2-r^2)

lemma realNumerator_identity (x y r X Y s : ℝ) :
    realNumerator x y r X Y s =
      ((C x-Polynomial.X)*powerPolynomial X Y s -
        (C X-Polynomial.X)*powerPolynomial x y r)^2 +
      (C y*powerPolynomial X Y s-C Y*powerPolynomial x y r)^2 := by
  simp [realNumerator,powerPolynomial,circleA,circleB,circleC,quad,
    map_add,map_sub,map_mul,map_pow,map_ofNat]
  ring

lemma powerPolynomial_eval (x y r t : ℝ) :
    (powerPolynomial x y r).eval t = (t-x)^2+y^2-r^2 := by
  simp [powerPolynomial,quad]
  ring

lemma inverted_center_distance_sq (x y r X Y s t : ℝ)
    (hf : (powerPolynomial x y r).eval t ≠ 0)
    (hg : (powerPolynomial X Y s).eval t ≠ 0) :
    ((x-t)/(powerPolynomial x y r).eval t -
       (X-t)/(powerPolynomial X Y s).eval t)^2 +
      (y/(powerPolynomial x y r).eval t-Y/(powerPolynomial X Y s).eval t)^2 =
      (realNumerator x y r X Y s).eval t /
        ((powerPolynomial x y r).eval t*(powerPolynomial X Y s).eval t)^2 := by
  rw [realNumerator_identity]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X]
  field_simp

noncomputable def circleVector (x y r : ℝ) : Fin 4 → ℝ :=
  ![1/r,x/r,y/r,(x^2+y^2-r^2)/r]

lemma circleVector_norm (x y r : ℝ) (hr : r ≠ 0) :
    DescartesReflection.circleNorm (circleVector x y r) = 1 := by
  simp [DescartesReflection.circleNorm,circleVector,Matrix.cons_val]
  field_simp
  ring

lemma circleVector_tangent (x y r X Y s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h : (x-X)^2+(y-Y)^2 = (r+s)^2) :
    DescartesReflection.twicePair (circleVector x y r) (circleVector X Y s) = -2 := by
  simp [DescartesReflection.twicePair,circleVector,Matrix.cons_val]
  field_simp
  linear_combination -h

/-- No five positive-radius, pairwise externally separated circles below the
line of inversion poles have all their pair-distance numerators square as
polynomial identities. Individual rational specializations are not excluded. -/
lemma five_separated_circles_no_universal_squares (x y r : Fin 5 → ℝ)
    (hr : ∀ i, 0 < r i) (hy : ∀ i, y i < -r i)
    (hsep : ∀ i j, i ≠ j → (r i+r j)^2 ≤ (x i-x j)^2+(y i-y j)^2) :
    ¬ (∀ i j, i ≠ j → IsSquare (realNumerator (x i) (y i) (r i) (x j) (y j) (r j))) := by
  intro hsq
  apply DescartesReflection.no_five_tangent (fun i => circleVector (x i) (y i) (r i))
  · intro i
    exact circleVector_norm _ _ _ (ne_of_gt (hr i))
  · intro i j hij
    have he : (x i-x j)^2+(y i-y j)^2 = (r i+r j)^2 := by
      apply le_antisymm ?_ (hsep i j hij)
      by_contra h
      exact separated_real_numerator_no_square (x i) (y i) (r i) (x j) (y j) (r j)
        (hr i) (hr j) (hy i) (hy j) (lt_of_not_ge h) (hsq i j hij)
    exact circleVector_tangent _ _ _ _ _ _ (ne_of_gt (hr i)) (ne_of_gt (hr j)) he

lemma five_separated_circles_no_ratFunc_squares (x y r : Fin 5 → ℝ)
    (hr : ∀ i, 0 < r i) (hy : ∀ i, y i < -r i)
    (hsep : ∀ i j, i ≠ j → (r i+r j)^2 ≤ (x i-x j)^2+(y i-y j)^2) :
    ¬ (∀ i j, i ≠ j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (realNumerator (x i) (y i) (r i) (x j) (y j) (r j)))) := by
  intro hsq
  exact five_separated_circles_no_universal_squares x y r hr hy hsep
    (fun i j hij => polynomial_square_of_ratFunc_square _ (hsq i j hij))

#print axioms realNumerator_identity
#print axioms inverted_center_distance_sq
#print axioms five_separated_circles_no_universal_squares
#print axioms five_separated_circles_no_ratFunc_squares
#print axioms separated_ratFunc_numerator_no_square
#print axioms separated_real_numerator_no_square
#print axioms circle_discriminant
#print axioms separated_circles_no_square
#print axioms quad_separable
#print axioms real_discriminant_square_norm
end Erdos213.CircleLineRigidity
