import Submission.SignedRankSix
import Mathlib.Tactic.NormNum.IsSquare

/-! A necessary square condition for rational unit directions perpendicular to
an affine moment. This does not rule out finite rational-distance extensions. -/

namespace Erdos213.SignedRankSix

lemma perpendicular_unit_square {R : Type*} [CommRing R] (D sx sy x y : R)
    (hperp : sx*x + D*sy*y = 0) (hunit : x^2 + D*y^2 = 1) :
    IsSquare (D*(sx^2 + D*sy^2)) := by
  refine ⟨D*(sx*y-sy*x), ?_⟩
  have h : D*(sx^2 + D*sy^2) = (D*(sx*y-sy*x))^2 := by
    linear_combination -D*(sx^2 + D*sy^2)*hunit + D*(sx*x + D*sy*y)*hperp
  simpa only [pow_two] using h

open scoped BigOperators

/-- The linearized distance equations and a signed-kernel relation force the
same perpendicular-unit square condition. This is an algebraic statement
about first-order data, not an assertion that such data lift to a curve. -/
lemma weighted_radial_tangent_square {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] (D X Y a0 : R) (k x y dr : ι → R)
    (hsum : ∑ i, k i = 0) (hderiv : ∑ i, k i * dr i = 0)
    (hfirst : ∀ i, dr i - a0 + x i*X + D*y i*Y = 0)
    (hunit : X^2 + D*Y^2 = 1) :
    IsSquare (D*((∑ i, k i*x i)^2 + D*(∑ i, k i*y i)^2)) := by
  have hd : (∑ i, k i*dr i) = (∑ i, k i)*a0 -
      (∑ i, k i*x i)*X - D*(∑ i, k i*y i)*Y := by
    calc
      (∑ i, k i*dr i) = ∑ i, (k i*a0 - k i*x i*X - D*(k i*y i)*Y) := by
        apply Finset.sum_congr rfl
        intro i _
        linear_combination k i * hfirst i
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  have hp : (∑ i, k i*x i)*X + D*(∑ i, k i*y i)*Y = 0 := by
    rw [hderiv, hsum, zero_mul] at hd
    linear_combination hd
  exact perpendicular_unit_square D _ _ X Y hp hunit

lemma moment2002_no_perpendicular_unit (x y : ℚ)
    (hunit : x^2 + 2002*y^2 = 1) :
    44317493*x + 2002*1895758*y ≠ 0 := by
  intro hp
  have hs := perpendicular_unit_square (2002 : ℚ) 44317493 1895758 x y hp hunit
  norm_num at hs

lemma moment77_no_perpendicular_unit (x y : ℚ)
    (hunit : x^2 + 77*y^2 = 1) :
    (-1302457427)*x + 77*1597588989*y ≠ 0 := by
  intro hp
  have hs := perpendicular_unit_square (77 : ℚ) (-1302457427) 1597588989 x y hp hunit
  norm_num at hs

#print axioms perpendicular_unit_square
#print axioms weighted_radial_tangent_square
#print axioms moment2002_no_perpendicular_unit
#print axioms moment77_no_perpendicular_unit
end Erdos213.SignedRankSix
