import Submission.PolynomialTwoAnchors
import Submission.PolynomialSquareValuesTests

/-! Controls that separate uniform polynomial paths from sparse parameters
and rational-function paths. None is an integral-distance GP construction. -/
namespace Erdos213.PolynomialTwoAnchorsControls
open Polynomial PolynomialTwoAnchors
noncomputable section

/-- A polynomial off the anchor line can have rational distances to BOTH
anchors at infinitely many integer parameters: a Pell sequence on the
perpendicular bisector. Thus "eventually every" cannot be weakened to
"infinitely many" in `eventual_two_anchor_classification`. -/
theorem sparse_two_anchor_control :
    Set.Infinite {n : ℤ |
      IsSquare ((1/2 : ℚ)^2+2*((n : ℚ)/2)^2) ∧
      IsSquare (((1/2 : ℚ)-1)^2+2*((n : ℚ)/2)^2)} := by
  have hh := PolynomialSquareValuesTests.infinite_square_values_not_square.2
  apply hh.mono
  intro n hn
  have hs := hn.div (IsSquare.sq (2 : ℚ))
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] at hs
  constructor <;> convert hs using 1 <;> ring

lemma sparse_path_not_classified :
    ¬ ((C (1/2 : ℚ)*X : ℚ[X])=0 ∨
      ((C (1/2 : ℚ) : ℚ[X]).natDegree=0 ∧
       (C (1/2 : ℚ)*X : ℚ[X]).natDegree=0)) := by
  have hd : (C (1/2 : ℚ)*X : ℚ[X]).natDegree=1 := natDegree_C_mul_X _ (by norm_num)
  intro h
  rcases h with h | h
  · have he := congrArg natDegree h
    simp only [hd,natDegree_zero] at he
    omega
  · omega

/-- There is no eventual interval of simultaneous rational distances on that
Pell control, even though the parameter set just proved is infinite. -/
theorem sparse_not_eventual :
    ¬ ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((1/2 : ℚ)^2+2*((n : ℚ)/2)^2) ∧
      IsSquare (((1/2 : ℚ)-1)^2+2*((n : ℚ)/2)^2) := by
  rintro ⟨N,hN⟩
  apply sparse_path_not_classified
  apply eventual_two_anchor_classification (C (1/2)) (C (1/2)*X) 2 (by norm_num)
  · refine ⟨N,?_⟩
    intro n hn
    simpa only [eval_C,eval_mul,eval_X,div_eq_mul_inv,mul_comm,one_mul] using (hN n hn).1
  · refine ⟨N,?_⟩
    intro n hn
    simpa only [eval_C,eval_mul,eval_X,div_eq_mul_inv,mul_comm,one_mul] using (hN n hn).2

/-- A noncircular ellipse with foci (0,0) and (1,0). Its rational
parametrization has rational distances to both foci for every rational t. -/
def ex (t : ℚ) : ℚ := 1/2+(5/8)*(1-t^2)/(1+t^2)
def ey (t : ℚ) : ℚ := (3/4)*t/(1+t^2)

lemma ellipse_radii (t : ℚ) :
    (ex t)^2+(ey t)^2=((9+t^2)/(8*(1+t^2)))^2 ∧
    (ex t-1)^2+(ey t)^2=((1+9*t^2)/(8*(1+t^2)))^2 := by
  have ht : 1+t^2 ≠ 0 := by positivity
  dsimp [ex,ey]
  constructor <;> field_simp <;> ring

theorem rational_ellipse_two_anchors (t : ℚ) :
    IsSquare ((ex t)^2+(ey t)^2) ∧ IsSquare ((ex t-1)^2+(ey t)^2) := by
  rw [(ellipse_radii t).1,(ellipse_radii t).2]
  exact ⟨IsSquare.sq _,IsSquare.sq _⟩

/-- The ellipse control is genuinely noncollinear, but its pairwise distances
are not all rational. It is not a counterexample to any GP bound. -/
lemma ellipse_scope_control :
    (ex 1-ex 0)*(ey (-1)-ey 0)-(ey 1-ey 0)*(ex (-1)-ex 0) ≠ 0 ∧
    ¬ IsSquare ((ex 1-ex 0)^2+(ey 1-ey 0)^2) := by
  norm_num [ex,ey]

/-- One-anchor polynomial growth is also possible; the second anchor is
essential to the classification. -/
lemma parabola_one_anchor :
    IsSquare (((X : ℚ[X])^2-1)^2+(2*X)^2) ∧
    ¬ IsSquare ((((X : ℚ[X])^2-1)-1)^2+(2*X)^2) := by
  constructor
  · refine ⟨X^2+1,?_⟩
    ring
  · intro h
    have he := h.map (evalRingHom (1 : ℚ))
    norm_num at he

/-- Constant off-axis paths explain why the classification has a constant
alternative rather than concluding that every path lies on the anchor line. -/
lemma constant_off_axis_control :
    (C (3/8 : ℚ) : ℚ[X]) ≠ 0 ∧
    IsSquare ((C (1/2 : ℚ) : ℚ[X])^2+(C (3/8 : ℚ))^2) ∧
    IsSquare (((C (1/2 : ℚ) : ℚ[X])-1)^2+(C (3/8 : ℚ))^2) := by
  refine ⟨by simp,?_,?_⟩
  · refine ⟨C (5/8),?_⟩
    rw [← map_pow,← map_pow,← map_add,← map_mul]
    norm_num
  · refine ⟨C (5/8),?_⟩
    rw [← map_one C,← map_sub,← map_pow,← map_pow,← map_add,← map_mul]
    norm_num

/-- Two parameters in the sparse two-anchor control already have an
irrational mutual distance. The control is not a rational-distance clique. -/
lemma sparse_pair_control :
    IsSquare ((1/2 : ℚ)^2+2*((0 : ℚ)/2)^2) ∧
    IsSquare ((1/2 : ℚ)^2+2*((2 : ℚ)/2)^2) ∧
    ¬ IsSquare (2*((2 : ℚ)/2-0)^2) := by norm_num

#print axioms sparse_two_anchor_control
#print axioms sparse_not_eventual
#print axioms rational_ellipse_two_anchors
#print axioms ellipse_scope_control
#print axioms parabola_one_anchor
#print axioms constant_off_axis_control
#print axioms sparse_pair_control
end
end Erdos213.PolynomialTwoAnchorsControls
