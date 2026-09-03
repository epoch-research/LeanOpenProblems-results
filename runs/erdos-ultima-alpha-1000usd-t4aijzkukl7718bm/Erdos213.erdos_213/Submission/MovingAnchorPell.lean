import Submission.MovingAnchorPolynomial

/-! Two moving anchors and the polynomial Pell reduction.
These statements concern universal polynomial distance identities, not merely
square values at a specialization, and do not settle Erdős Problem 213. -/
namespace Erdos213.MovingAnchorPell
open Polynomial Filter
noncomputable section
set_option maxHeartbeats 2000000

/-- In the polynomial Heron identity, at least one signed length sum has
degree no greater than the anchor displacement. -/
lemma heron_degree_bound (u v y H : ℝ[X]) (hH : H≠0)
    (h : 4*H^2*y^2=(u^2-H^2)*(H^2-v^2)) :
    u.natDegree≤H.natDegree ∨ v.natDegree≤H.natDegree := by
  by_contra hh
  have hu : H.natDegree<u.natDegree := by omega
  have hv : H.natDegree<v.natDegree := by omega
  have hU := (u.abs_div_tendsto_atTop_of_degree_gt H (degree_lt_degree hu) hH).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hV := (v.abs_div_tendsto_atTop_of_degree_gt H (degree_lt_degree hv) hH).eventually
    (eventually_ge_atTop (2 : ℝ))
  obtain ⟨t,htU,htV,htH⟩ := (hU.and (hV.and (H.eventually_no_roots hH))).exists
  change H.eval t≠0 at htH
  rw [abs_div] at htU htV
  have hUP := (le_div_iff₀ (abs_pos.mpr htH)).mp htU
  have hVP := (le_div_iff₀ (abs_pos.mpr htH)).mp htV
  have hUs : 0<(u.eval t)^2-(H.eval t)^2 := by
    nlinarith [sq_abs (u.eval t),sq_abs (H.eval t),sq_pos_of_ne_zero htH,
      mul_nonneg (sub_nonneg.mpr hUP) (show 0≤|u.eval t|+2*|H.eval t| by positivity)]
  have hVs : 0<(v.eval t)^2-(H.eval t)^2 := by
    nlinarith [sq_abs (v.eval t),sq_abs (H.eval t),sq_pos_of_ne_zero htH,
      mul_nonneg (sub_nonneg.mpr hVP) (show 0≤|v.eval t|+2*|H.eval t| by positivity)]
  have he := congrArg (Polynomial.eval t) h
  simp only [eval_mul,eval_ofNat,eval_pow,eval_sub] at he
  have hy : 0≤4*(H.eval t)^2*(y.eval t)^2 := by positivity
  nlinarith [mul_pos hUs hVs]

lemma heron_identity {R : Type*} [CommRing R] (x y d e H : R)
    (h0 : x^2+y^2=d^2) (h1 : (x-H)^2+y^2=e^2) :
    4*H^2*y^2=((d+e)^2-H^2)*(H^2-(d-e)^2) := by
  have hx : 2*H*x=d^2-e^2+H^2 := by linear_combination h0-h1
  calc
    _ = 4*H^2*d^2-(2*H*x)^2 := by linear_combination 4*H^2*h0
    _ = 4*H^2*d^2-(d^2-e^2+H^2)^2 := by rw [hx]
    _ = _ := by ring

/-- The signed square roots of polynomial distances to `0,H` have a sum
or difference whose degree is at most that of `H`. -/
theorem signed_length_degree_bound (x y d e H : ℝ[X]) (hH : H≠0)
    (h0 : x^2+y^2=d^2) (h1 : (x-H)^2+y^2=e^2) :
    (d+e).natDegree≤H.natDegree ∨ (d-e).natDegree≤H.natDegree :=
  heron_degree_bound (d+e) (d-e) y H hH (heron_identity x y d e H h0 h1)

/-- For anchors `0,t`, one can choose signs of the length polynomials so
that their difference is affine. -/
theorem affine_signed_lengths (x y : ℝ[X])
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2)) :
    ∃ d e : ℝ[X], x^2+y^2=d^2 ∧ (x-X)^2+y^2=e^2 ∧
      (d-e).natDegree≤1 := by
  obtain ⟨d,hd⟩ := h0
  obtain ⟨e,he⟩ := h1
  rw [←pow_two] at hd he
  rcases signed_length_degree_bound x y d e X X_ne_zero hd he with h | h
  · refine ⟨d,-e,hd,?_,?_⟩
    · simpa using he
    · simpa using h
  · exact ⟨d,e,hd,he,by simpa using h⟩

/-- Factoring over `ℂ` bounds both unknown degrees by the degree of the
nonzero right-hand side of a constant-coefficient polynomial Pell equation. -/
lemma complex_pell_degree_bound (p q R : ℂ[X]) (c : ℂ) (hc : c≠0) (hR : R≠0)
    (h : p^2-C c*q^2=R) : p.natDegree≤R.natDegree ∧ q.natDegree≤R.natDegree := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0<(2 : ℕ))
  have hs0 : s≠0 := by intro hz; simp [hz] at hs; exact hc hs.symm
  let u := p-C s*q
  let v := p+C s*q
  have huv : u*v=R := by
    calc
      _ = p^2-C (s^2)*q^2 := by dsimp [u,v]; rw [map_pow]; ring
      _ = R := by rw [hs,h]
  have hu : u≠0 := by intro hz; apply hR; rw [hz,zero_mul] at huv; exact huv.symm
  have hv : v≠0 := by intro hz; apply hR; rw [hz,mul_zero] at huv; exact huv.symm
  have hdeg : u.natDegree+v.natDegree=R.natDegree := by rw [←natDegree_mul hu hv,huv]
  have hp : C (2 : ℂ)*p=v+u := by dsimp [u,v]; norm_num only [map_ofNat]; ring
  have hq : C (2*s)*q=v-u := by dsimp [u,v]; rw [map_mul]; norm_num only [map_ofNat]; ring
  constructor
  · calc
      _ = (C (2 : ℂ)*p).natDegree := by rw [natDegree_C_mul (by norm_num)]
      _ = (v+u).natDegree := by rw [hp]
      _ ≤ max v.natDegree u.natDegree := natDegree_add_le _ _
      _ ≤ R.natDegree := by omega
  · calc
      _ = (C (2*s)*q).natDegree := by rw [natDegree_C_mul (mul_ne_zero (by norm_num) hs0)]
      _ = (v-u).natDegree := by rw [hq]
      _ ≤ max v.natDegree u.natDegree := natDegree_sub_le _ _
      _ ≤ R.natDegree := by omega

lemma real_pell_X_degree_bound (p q : ℝ[X]) (c : ℝ) (hc : c≠0)
    (h : p^2-C c*q^2=X^2) : p.natDegree≤2 ∧ q.natDegree≤2 := by
  have hm := congrArg (Polynomial.map Complex.ofRealHom) h
  simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_mul,map_C,map_X] at hm
  have hh := complex_pell_degree_bound _ _ _ (c : ℂ) (by exact_mod_cast hc)
    (pow_ne_zero 2 X_ne_zero) hm
  simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective,natDegree_X_pow] using hh

/-- An affine signed-length difference vanishing at the anchor collision
cannot support a genuinely higher-degree off-axis motion. -/
lemma zero_intercept_degree_bound (x y d e : ℝ[X]) (a : ℝ) (hy : y≠0)
    (h0 : x^2+y^2=d^2) (h1 : (x-X)^2+y^2=e^2) (hA : d-e=C a*X) :
    x.natDegree≤2 ∧ y.natDegree≤2 := by
  let U := d+e
  have he : 4*y^2=C (1-a^2)*(U^2-X^2) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero : (X : ℝ[X])≠0))
    have hh := heron_identity x y d e X h0 h1
    rw [hA] at hh
    dsimp [U]
    simp only [map_sub,map_one,map_pow] at *
    linear_combination hh
  have ha : 1-a^2≠0 := by
    intro hz
    rw [hz,map_zero,zero_mul] at he
    have hh : y^2=0 := (mul_eq_zero.mp he).resolve_left (by norm_num)
    exact hy (eq_zero_of_pow_eq_zero hh)
  have he' : U^2-C (4/(1-a^2))*y^2=X^2 := by
    have hcc : C (1-a^2)*C (4/(1-a^2))=(4 : ℝ[X]) := by
      rw [←map_mul,mul_div_cancel₀ _ ha]; simp only [map_ofNat]
    apply mul_left_cancel₀ (C_ne_zero.mpr ha)
    linear_combination -he - y^2*hcc
  obtain ⟨hU,hy2⟩ := real_pell_X_degree_bound U y (4/(1-a^2))
    (div_ne_zero (by norm_num) ha) he'
  refine ⟨?_,hy2⟩
  have hx : C (2 : ℝ)*x=X+C a*U := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X])≠0)
    have hp : (d-e)*(d+e)=X*(2*x-X) := by linear_combination h1-h0
    rw [hA] at hp
    dsimp [U]
    norm_num only [map_ofNat]
    linear_combination -hp
  calc
    _ = (C (2 : ℝ)*x).natDegree := by rw [natDegree_C_mul (by norm_num)]
    _ = (X+C a*U).natDegree := by rw [hx]
    _ ≤ max (X : ℝ[X]).natDegree (C a*U).natDegree := natDegree_add_le _ _
    _ ≤ 2 := max_le (by simp) ((natDegree_C_mul_le _ _).trans hU)

/-- Nonzero-intercept affine signed lengths give a polynomial Pell equation.
The zero-intercept case is treated separately above. -/
lemma nonzero_intercept_pell (x y d e : ℝ[X]) (a b : ℝ) (hb : b≠0)
    (h0 : x^2+y^2=d^2) (h1 : (x-X)^2+y^2=e^2)
    (hA : d-e=C a*X+C b) :
    ∃ u v : ℝ[X],
      2*x=X+(C a*X+C b)*u ∧
      2*y=(X^2-(C a*X+C b)^2)*v ∧
      u^2-(X^2-(C a*X+C b)^2)*v^2=1 := by
  let A := C a*X+C b
  let K := X^2-A^2
  have hprod : (d-e)*(d+e)=X*(2*x-X) := by linear_combination h1-h0
  have hcoeff : b*(d+e).coeff 0=0 := by
    have hh := congrArg (fun p : ℝ[X] => p.coeff 0) hprod
    rw [hA] at hh
    simpa using hh
  obtain ⟨u,hu⟩ := X_dvd_iff.mpr ((mul_eq_zero.mp hcoeff).resolve_left hb)
  have hx : 2*x=X+A*u := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X])≠0)
    rw [hA,hu] at hprod
    dsimp [A]
    linear_combination -hprod
  have he : 4*y^2=K*(u^2-1) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero : (X : ℝ[X])≠0))
    have hh := heron_identity x y d e X h0 h1
    rw [hA,hu] at hh
    dsimp [K,A]
    linear_combination hh
  have hK : K≠0 := by
    intro hz
    have hh := congrArg (Polynomial.eval 0) hz
    have hbb : b^2=0 := by simpa [K,A] using hh
    exact hb (eq_zero_of_pow_eq_zero hbb)
  have hsf : Squarefree K := by
    have hk : K=CircleLineRigidity.quad (1-a^2) (-2*a*b) (-b^2) := by
      dsimp [K,A,CircleLineRigidity.quad]
      simp only [map_sub,map_one,map_pow,map_mul,map_neg,map_ofNat]
      ring
    rw [hk]
    apply (CircleLineRigidity.quad_separable _ _ _ ?_).squarefree
    have hh : (-2*a*b)^2-4*(1-a^2)*(-b^2)=4*b^2 := by ring
    rw [hh]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  have hd : K ∣ (2*y)^2 := ⟨u^2-1,by linear_combination he⟩
  obtain ⟨v,hv⟩ := (hsf.dvd_pow_iff_dvd (by decide : (2 : ℕ)≠0)).mp hd
  refine ⟨u,v,hx,hv,?_⟩
  change u^2-K*v^2=1
  apply mul_left_cancel₀ hK
  have hs := congrArg (fun p : ℝ[X] => p^2) hv
  linear_combination -he + hs

/-- Every off-axis motion of degree greater than two, with square polynomial
distances to `0,t`, has the displayed quadratic-coefficient Pell normal form.
This does not assert compatibility between two different exterior motions. -/
theorem high_degree_pell_normal_form (x y : ℝ[X]) (hy : y≠0)
    (hdeg : 2<x.natDegree ∨ 2<y.natDegree)
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2)) :
    ∃ a b : ℝ, ∃ u v : ℝ[X], b≠0 ∧
      2*x=X+(C a*X+C b)*u ∧
      2*y=(X^2-(C a*X+C b)^2)*v ∧
      u^2-(X^2-(C a*X+C b)^2)*v^2=1 := by
  obtain ⟨d,e,hd,he,hdegree⟩ := affine_signed_lengths x y h0 h1
  obtain ⟨a,b,hA⟩ := exists_eq_X_add_C_of_natDegree_le_one hdegree
  have hb : b≠0 := by
    intro hz
    have hA' : d-e=C a*X := by simpa [hz] using hA
    obtain ⟨hx,hy2⟩ := zero_intercept_degree_bound x y d e a hy hd he hA'
    omega
  obtain ⟨u,v,hx,hy2,hpell⟩ := nonzero_intercept_pell x y d e a b hb hd he hA
  exact ⟨a,b,u,v,hb,hx,hy2,hpell⟩

/-- A nonconstant polynomial coefficient admitting a nontrivial real Pell
solution has positive leading coefficient and even degree. -/
lemma pell_degree_and_leadingCoeff (K u v : ℝ[X]) (hK : 0<K.natDegree) (hv : v≠0)
    (h : u^2-K*v^2=1) : Even K.natDegree ∧ 0<K.leadingCoeff := by
  have hK0 : K≠0 := by intro hz; simp [hz] at hK
  have hv2 : v^2≠0 := pow_ne_zero 2 hv
  have hd : 0<(K*v^2).natDegree := by rw [natDegree_mul hK0 hv2,natDegree_pow]; omega
  have he : u^2=K*v^2+1 := by linear_combination h
  have hdeg : 2*u.natDegree=K.natDegree+2*v.natDegree := by
    have hh := congrArg natDegree he
    rw [natDegree_pow,natDegree_add_eq_left_of_natDegree_lt (by simpa using hd),
      natDegree_mul hK0 hv2,natDegree_pow] at hh
    omega
  have hu : u≠0 := by intro hz; simp [hz] at hdeg; omega
  have hl : u.leadingCoeff^2=K.leadingCoeff*v.leadingCoeff^2 := by
    have hh := congrArg leadingCoeff he
    rw [leadingCoeff_pow,leadingCoeff_add_of_degree_lt' (degree_lt_degree (by simpa using hd)),
      leadingCoeff_mul,leadingCoeff_pow] at hh
    exact hh
  constructor
  · exact ⟨u.natDegree-v.natDegree,by omega⟩
  · have hp : 0<K.leadingCoeff*v.leadingCoeff^2 := by
      rw [←hl]
      exact sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hu)
    exact (mul_pos_iff_of_pos_right (sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hv))).mp hp

lemma pell_slope_bound (a b : ℝ) (hb : b≠0) (u v : ℝ[X]) (hv : v≠0)
    (h : u^2-(X^2-(C a*X+C b)^2)*v^2=1) : a^2<1 := by
  let K : ℝ[X] := X^2-(C a*X+C b)^2
  have hk : K=C (1-a^2)*X^2+C (-2*a*b)*X+C (-b^2) := by
    dsimp [K]
    simp only [map_sub,map_one,map_pow,map_mul,map_neg,map_ofNat]
    ring
  by_cases ha : 1-a^2=0
  · have ha0 : a≠0 := by intro hz; simp [hz] at ha
    have hab : -2*a*b≠0 := mul_ne_zero (mul_ne_zero (by norm_num) ha0) hb
    have hdeg : K.natDegree=1 := by rw [hk,ha,map_zero,zero_mul,zero_add]; exact natDegree_linear hab
    obtain ⟨⟨r,hr⟩,_⟩ := pell_degree_and_leadingCoeff K u v (by omega) hv h
    omega
  · have hdeg : K.natDegree=2 := by rw [hk]; exact natDegree_quadratic ha
    have hlc : K.leadingCoeff=1-a^2 := by rw [hk]; exact leadingCoeff_quadratic ha
    have hh := (pell_degree_and_leadingCoeff K u v (by omega) hv h).2
    rw [hlc] at hh
    linarith

/-- The high-degree Pell normal form has a genuine two-root, positive-leading
quadratic coefficient. The slope bound is forced, not an extra assumption. -/
theorem high_degree_pell_normal_form_bounded (x y : ℝ[X]) (hy : y≠0)
    (hdeg : 2<x.natDegree ∨ 2<y.natDegree)
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2)) :
    ∃ a b : ℝ, ∃ u v : ℝ[X], b≠0 ∧ a^2<1 ∧
      2*x=X+(C a*X+C b)*u ∧
      2*y=(X^2-(C a*X+C b)^2)*v ∧
      u^2-(X^2-(C a*X+C b)^2)*v^2=1 := by
  obtain ⟨a,b,u,v,hb,hx,hy2,hpell⟩ := high_degree_pell_normal_form x y hy hdeg h0 h1
  have hv : v≠0 := by
    intro hz
    rw [hz,mul_zero] at hy2
    exact hy ((mul_eq_zero.mp hy2).resolve_left (by norm_num))
  exact ⟨a,b,u,v,hb,pell_slope_bound a b hb u v hv hpell,hx,hy2,hpell⟩

/-- A Pell solution is sufficient for square distances to two anchors.
Doubled coordinates avoid any division-by-two hypothesis on the ring. -/
lemma pell_motion_squares {R : Type*} [CommRing R] (t A u v : R)
    (h : u^2-(t^2-A^2)*v^2=1) :
    (t+A*u)^2+((t^2-A^2)*v)^2=(t*u+A)^2 ∧
    (t+A*u-2*t)^2+((t^2-A^2)*v)^2=(t*u-A)^2 := by
  constructor <;> linear_combination -(t^2-A^2)*h

/-- Multiplication in a quadratic algebra preserves its norm-one equation. -/
lemma pell_step {R : Type*} [CommRing R] (K L q u v : R)
    (hL : L^2-K*q^2=1) (hu : u^2-K*v^2=1) :
    (L*u+K*q*v)^2-K*(q*u+L*v)^2=1 := by
  calc
    _ = (L^2-K*q^2)*(u^2-K*v^2) := by ring
    _ = 1 := by rw [hL,hu,mul_one]

def pellPower {R : Type*} [CommRing R] (K L q : R) : ℕ → R×R
  | 0 => (1,0)
  | n+1 => let p := pellPower K L q n
      (L*p.1+K*q*p.2,q*p.1+L*p.2)

lemma pellPower_norm {R : Type*} [CommRing R] (K L q : R)
    (h : L^2-K*q^2=1) (n : ℕ) :
    (pellPower K L q n).1^2-K*(pellPower K L q n).2^2=1 := by
  induction n with
  | zero => simp [pellPower]
  | succ n ih => exact pell_step K L q _ _ h ih

lemma pell_seed {R : Type*} [Field R] (t a b s : R) (hb : b≠0)
    (h : a^2+s^2=1) :
    ((1-a^2)*t/b-a)^2-(t^2-(a*t+b)^2)*(s/b)^2=1 := by
  have hs : s^2=1-a^2 := by linear_combination h
  field_simp
  rw [hs]
  ring

/-- An explicit, all-degree family of individual exterior motions. No claim
of mutual compatibility among different powers is made. -/
theorem pell_power_motion_squares {R : Type*} [Field R]
    (t a b s : R) (hb : b≠0) (h : a^2+s^2=1) (n : ℕ) :
    let A := a*t+b
    let K := t^2-A^2
    let p := pellPower K ((1-a^2)*t/b-a) (s/b) n
    (t+A*p.1)^2+(K*p.2)^2=(t*p.1+A)^2 ∧
    (t+A*p.1-2*t)^2+(K*p.2)^2=(t*p.1-A)^2 := by
  dsimp only
  exact pell_motion_squares t (a*t+b) _ _
    (pellPower_norm _ _ _ (pell_seed t a b s hb h) n)

lemma high_degree_pell_normal_form_ratFunc (x y : ℝ[X]) (hy : y≠0)
    (hdeg : 2<x.natDegree ∨ 2<y.natDegree)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (x^2+y^2)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) ((x-X)^2+y^2))) :
    ∃ a b : ℝ, ∃ u v : ℝ[X], b≠0 ∧ a^2<1 ∧
      2*x=X+(C a*X+C b)*u ∧
      2*y=(X^2-(C a*X+C b)^2)*v ∧
      u^2-(X^2-(C a*X+C b)^2)*v^2=1 :=
  high_degree_pell_normal_form_bounded x y hy hdeg
    (CircleLineRigidity.polynomial_square_of_ratFunc_square _ h0)
    (CircleLineRigidity.polynomial_square_of_ratFunc_square _ h1)

#print axioms heron_degree_bound
#print axioms affine_signed_lengths
#print axioms high_degree_pell_normal_form
#print axioms high_degree_pell_normal_form_bounded
#print axioms pell_power_motion_squares
#print axioms high_degree_pell_normal_form_ratFunc
end
end Erdos213.MovingAnchorPell
