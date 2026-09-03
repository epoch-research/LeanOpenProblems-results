import FormalConjecturesUtil

/-! Polynomial square obstructions used in the quartic residual analysis.
These are not bounds for arbitrary rational-distance configurations. -/
namespace Erdos213.QuarticCoefficientObstructions
open Polynomial
set_option maxHeartbeats 4000000

private lemma quadratic_repr {p : ℚ[X]} (hp : p.natDegree ≤ 2) :
    p = C (p.coeff 2)*X^2+C (p.coeff 1)*X+C (p.coeff 0) := by
  calc
    p = ∑ i ∈ Finset.range 3, C (p.coeff i)*X^i :=
      p.as_sum_range_C_mul_X_pow' (show p.natDegree < 3 by omega)
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        mul_one, pow_one]
      ring

private lemma quadratic_square_coefficients (a b c : ℚ) :
    (C a*X^2+C b*X+C c : ℚ[X])^2 =
    C (a^2)*X^4+C (2*a*b)*X^3+C (b^2+2*a*c)*X^2+C (2*b*c)*X+C (c^2) := by
  simp only [map_add,map_mul,map_pow,map_ofNat]
  ring

/-- A quartic with constant coefficient one, zero linear coefficient, and
nonzero cubic coefficient cannot be a square if its quadratic square root
would have nonzero constant coefficient and zero linear coefficient. -/
theorem pole_quartic_not_square {a : ℚ} (ha : a ≠ 0) (r : ℚ) :
    ¬ IsSquare ((C a*X^2+1)^2+C (2*a)*(X+C r)*X^2 : ℚ[X]) := by
  rintro ⟨p,hp⟩
  rw [← pow_two] at hp
  have hd : p.natDegree ≤ 2 := by
    have he : (p^2).natDegree ≤ 4 := by rw [← hp]; compute_degree
    rw [natDegree_pow] at he
    omega
  rw [quadratic_repr hd,quadratic_square_coefficients] at hp
  have hid : ((C a*X^2+1)^2+C (2*a)*(X+C r)*X^2 : ℚ[X]) =
      C (a^2)*X^4+C (2*a)*X^3+C (2*a*(r+1))*X^2+1 := by
    simp only [map_mul,map_add,map_pow,map_ofNat,map_one]
    ring
  rw [hid] at hp
  have h0 := congrArg (fun q : ℚ[X] => q.coeff 0) hp
  have h1 := congrArg (fun q : ℚ[X] => q.coeff 1) hp
  have h3 := congrArg (fun q : ℚ[X] => q.coeff 3) hp
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,coeff_one] at h0 h1 h3
  norm_num at h0 h1 h3
  have hc : p.coeff 0 ≠ 0 := by intro h; simp [h] at h0
  have hb : p.coeff 1 = 0 := h1.resolve_right hc
  apply ha
  simp [hb] at h3
  linarith

/-- Coefficient-level form of the obstruction at a critical supported value.
The hypotheses are exactly the nonautomatic coefficients of a proposed
quadratic square root of ((X-u)^2+aX^2)^2+8aX(X-u)^2. -/
lemma critical_coefficients_impossible {a u c b d : ℚ}
    (ha : a ≠ 0) (hu : u ≠ 0)
    (h0 : c^2 = u^4)
    (h1 : 2*b*c = -4*u^3+8*a*u^2)
    (h2 : b^2+2*d*c = (6+2*a)*u^2-16*a*u)
    (h3 : 2*d*b = -4*u*(a+1)+8*a)
    (h4 : d^2 = (a+1)^2) : False := by
  have hc : c = u^2 ∨ c = -(u^2) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith only [h0])
  have helper (c b d : ℚ) (hc : c = u^2)
      (h1 : 2*b*c = -4*u^3+8*a*u^2)
      (h2 : b^2+2*d*c = (6+2*a)*u^2-16*a*u)
      (h3 : 2*d*b = -4*u*(a+1)+8*a)
      (h4 : d^2 = (a+1)^2) : False := by
    subst c
    have hb : b = 4*a-2*u := by
      apply mul_right_cancel₀ (pow_ne_zero 2 hu)
      linear_combination h1 / 2
    subst b
    have hd : d = a+1 ∨ d = -(a+1) := sq_eq_sq_iff_eq_or_eq_neg.mp h4
    rcases hd with hd | hd
    · rw [hd] at h3
      have hz : a^2 = 0 := by nlinarith only [h3]
      exact ha (eq_zero_of_pow_eq_zero hz)
    · rw [hd] at h2 h3
      have hu' : u*(a+1)=a*(a+2) := by nlinarith only [h3]
      have ha' : (a+1)*u^2=4*a^2 := by nlinarith only [h2]
      have he : a^4=0 := by
        linear_combination (congrArg (fun z : ℚ => z*(a+1)) ha') -
          (congrArg (fun z : ℚ => z^2) hu')
      exact ha (eq_zero_of_pow_eq_zero he)
  rcases hc with hc | hc
  · exact helper c b d hc h1 h2 h3 h4
  · refine helper (-c) (-b) (-d) ?_ ?_ ?_ ?_ ?_
    · rw [hc,neg_neg]
    · convert h1 using 1
      ring
    · convert h2 using 1
      ring
    · convert h3 using 1
      ring
    · simpa only [neg_sq] using h4

/-- Uniform in the rational parameters, with no bound on a proposed square
root: its degree is forced to be at most two by the identity. -/
theorem critical_quartic_not_square {a u : ℚ} (ha : a ≠ 0) (hu : u ≠ 0) :
    ¬ IsSquare ((((X-C u)^2+C a*X^2)^2)+C (8*a)*X*(X-C u)^2 : ℚ[X]) := by
  rintro ⟨p,hp⟩
  rw [← pow_two] at hp
  have hd : p.natDegree ≤ 2 := by
    have he : (p^2).natDegree ≤ 4 := by rw [← hp]; compute_degree
    rw [natDegree_pow] at he
    omega
  rw [quadratic_repr hd,quadratic_square_coefficients] at hp
  have hid : ((((X-C u)^2+C a*X^2)^2)+C (8*a)*X*(X-C u)^2 : ℚ[X]) =
      C ((a+1)^2)*X^4+C (-4*u*(a+1)+8*a)*X^3+
      C ((6+2*a)*u^2-16*a*u)*X^2+C (-4*u^3+8*a*u^2)*X+C (u^4) := by
    simp only [map_mul,map_add,map_sub,map_neg,map_pow,map_ofNat,map_one]
    ring
  rw [hid] at hp
  have h0 := congrArg (fun q : ℚ[X] => q.coeff 0) hp
  have h1 := congrArg (fun q : ℚ[X] => q.coeff 1) hp
  have h2 := congrArg (fun q : ℚ[X] => q.coeff 2) hp
  have h3 := congrArg (fun q : ℚ[X] => q.coeff 3) hp
  have h4 := congrArg (fun q : ℚ[X] => q.coeff 4) hp
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] at h0 h1 h2 h3 h4
  norm_num at h0 h1 h2 h3 h4
  refine critical_coefficients_impossible ha hu (c := p.coeff 0)
    (b := p.coeff 1) (d := p.coeff 2) ?_ ?_ ?_ ?_ ?_
  · exact h0.symm
  · linear_combination -h1
  · exact h2.symm
  · linear_combination -h3
  · exact h4.symm

/-- If two polynomial squares differ by a nonzero polynomial of degree at
most one, both square roots have degree at most one. -/
lemma linear_difference_squares_degree {R S D : ℚ[X]} (hD : D ≠ 0)
    (hd : D.natDegree ≤ 1) (he : R^2-S^2=D) :
    R.natDegree ≤ 1 ∧ S.natDegree ≤ 1 := by
  have hprod : (R-S)*(R+S)=D := by rw [← he]; ring
  have hm : (R-S).natDegree ≤ 1 :=
    (natDegree_le_of_dvd ⟨R+S,hprod.symm⟩ hD).trans hd
  have hp : (R+S).natDegree ≤ 1 :=
    (natDegree_le_of_dvd ⟨R-S,by rw [mul_comm]; exact hprod.symm⟩ hD).trans hd
  constructor
  · have hh : ((R+S)+(R-S)).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le hp hm)
    have hi : (R+S)+(R-S)=C (2 : ℚ)*R := by
      rw [show (2 : ℚ) = 1+1 by norm_num, map_add, map_one]
      ring
    rw [hi,natDegree_C_mul (by norm_num : (2 : ℚ) ≠ 0)] at hh
    exact hh
  · have hh : ((R+S)-(R-S)).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le hp hm)
    have hi : (R+S)-(R-S)=C (2 : ℚ)*S := by
      rw [show (2 : ℚ) = 1+1 by norm_num, map_add, map_one]
      ring
    rw [hi,natDegree_C_mul (by norm_num : (2 : ℚ) ≠ 0)] at hh
    exact hh

/-- A useful all-degree obstruction: the two differences cannot both be
polynomial squares when B has degree at least two. -/
theorem two_shifted_square_differences {a : ℚ} (ha : a ≠ 0) {B : ℚ[X]}
    (hB : 2 ≤ B.natDegree) :
    ¬ (IsSquare (B^2-C a*X^2) ∧ IsSquare (B^2-C a*(X+1)^2)) := by
  rintro ⟨⟨R,hR⟩,⟨S,hS⟩⟩
  rw [← pow_two] at hR hS
  let D : ℚ[X] := C (2*a)*X+C a
  have hD : D ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℚ[X] => p.coeff 1) h
    simp only [D,coeff_add,coeff_C_mul,coeff_X,coeff_C,coeff_zero] at he
    norm_num at he
    exact ha he
  have hd : D.natDegree ≤ 1 := by unfold D; compute_degree
  have he : R^2-S^2=D := by
    dsimp [D]
    simp only [map_mul,map_ofNat]
    linear_combination -hR+hS
  have hr := (linear_difference_squares_degree hD hd he).1
  have hbsq : B^2=R^2+C a*X^2 := by linear_combination hR
  have hb : (B^2).natDegree ≤ 2 := by
    rw [hbsq]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · rw [natDegree_pow]
      omega
    · compute_degree
  rw [natDegree_pow] at hb
  omega

/-- Constant-denominator chart of the critical-value pencil. -/
theorem critical_constant_not_square {a : ℚ} (ha : a ≠ 0) :
    ¬ IsSquare ((1+C a*X^2)^2+C (8*a)*X : ℚ[X]) := by
  rintro ⟨p,hp⟩
  rw [← pow_two] at hp
  have hD : (C (8*a)*X : ℚ[X]) ≠ 0 := by
    apply mul_ne_zero
    · simp only [ne_eq,C_eq_zero]
      exact mul_ne_zero (by norm_num) ha
    · exact X_ne_zero
  have hd : (C (8*a)*X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  have he : p^2-(1+C a*X^2)^2=C (8*a)*X := by linear_combination -hp
  have hB := (linear_difference_squares_degree hD hd he).2
  have hcoeff : ((1+C a*X^2 : ℚ[X]).coeff 2) ≠ 0 := by
    simpa only [coeff_add,coeff_one,coeff_C_mul,coeff_X_pow,
      show (2 : ℕ) ≠ 0 by decide, if_false, if_true, mul_one, zero_add] using ha
  have hlo := le_natDegree_of_ne_zero hcoeff
  omega

#print axioms pole_quartic_not_square
#print axioms critical_coefficients_impossible
#print axioms critical_quartic_not_square
#print axioms linear_difference_squares_degree
#print axioms two_shifted_square_differences
#print axioms critical_constant_not_square
end Erdos213.QuarticCoefficientObstructions
