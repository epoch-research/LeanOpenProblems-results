import FormalConjecturesUtil

/-! Rational-distance anchor points from squares in imaginary quadratic fields.
This is a construction tool, not a settlement of Erdős Problem 213. -/

namespace Erdos213.SquareMap

noncomputable def F (z : ℂ) : ℂ := 4*z^2/(1+z^2)^2

lemma one_sub_F (z : ℂ) (hz : 1+z^2≠0) :
    1-F z = ((1-z^2)/(1+z^2))^2 := by
  unfold F
  field_simp
  ring

lemma dist_zero (z : ℂ) : dist (F z) 0 =
    4*Complex.normSq z/Complex.normSq (1+z^2) := by
  simp only [F,dist_zero_right,norm_div,norm_mul,norm_pow]
  norm_num
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]

lemma dist_one (z : ℂ) (hz : 1+z^2≠0) : dist (F z) 1 =
    Complex.normSq (1-z^2)/Complex.normSq (1+z^2) := by
  rw [dist_comm,dist_eq_norm,one_sub_F z hz,norm_pow,norm_div,div_pow]
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]

lemma pair_difference (z w : ℂ) (hz : 1+z^2≠0) (hw : 1+w^2≠0) :
    F z-F w = 4*(z-w)*(z+w)*(1-z*w)*(1+z*w)/
      ((1+z^2)^2*(1+w^2)^2) := by
  unfold F
  field_simp
  ring

noncomputable def quad (D : ℕ) (x y : ℚ) : ℂ :=
  (x : ℂ)+(y : ℂ)*(Real.sqrt D : ℂ)*Complex.I

def normQ (D : ℕ) (x y : ℚ) : ℚ := x^2+(D : ℚ)*y^2

lemma normSq_quad (D : ℕ) (x y : ℚ) :
    Complex.normSq (quad D x y) = (normQ D x y : ℝ) := by
  simp only [quad,normQ,Complex.normSq_apply]
  simp
  nlinarith [Real.sq_sqrt (show 0≤(D : ℝ) by positivity)]

lemma square_quad (D : ℕ) (x y : ℚ) :
    (quad D x y)^2 = quad D (x^2-(D : ℚ)*y^2) (2*x*y) := by
  apply Complex.ext <;> simp [quad,pow_two]
  · nlinarith [Real.sq_sqrt (show 0≤(D : ℝ) by positivity)]
  · ring

lemma one_add_square_quad (D : ℕ) (x y : ℚ) :
    1+(quad D x y)^2 = quad D (1+x^2-(D : ℚ)*y^2) (2*x*y) := by
  rw [square_quad]
  simp [quad]
  ring

lemma one_sub_square_quad (D : ℕ) (x y : ℚ) :
    1-(quad D x y)^2 = quad D (1-x^2+(D : ℚ)*y^2) (-2*x*y) := by
  rw [square_quad]
  simp [quad]
  ring

lemma quad_anchor_distances (D : ℕ) (x y : ℚ)
    (hz : 1+(quad D x y)^2≠0) :
    dist (F (quad D x y)) 0 ∈ Set.range ((↑) : ℚ → ℝ) ∧
    dist (F (quad D x y)) 1 ∈ Set.range ((↑) : ℚ → ℝ) := by
  constructor
  · refine ⟨4*normQ D x y/normQ D (1+x^2-D*y^2) (2*x*y),?_⟩
    rw [dist_zero,one_add_square_quad,normSq_quad,normSq_quad]
    push_cast
    rfl
  · refine ⟨normQ D (1-x^2+D*y^2) (-2*x*y)/
      normQ D (1+x^2-D*y^2) (2*x*y),?_⟩
    rw [dist_one _ hz,one_add_square_quad,one_sub_square_quad,
      normSq_quad,normSq_quad]
    push_cast
    rfl

#print axioms one_sub_F
#print axioms pair_difference
#print axioms quad_anchor_distances

end Erdos213.SquareMap
