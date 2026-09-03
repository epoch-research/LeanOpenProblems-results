import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Square-class switching under inversion. These equivalences do not assert
existence of a rational-distance configuration. -/
namespace Erdos213.SquareClassProjection

lemma square_ratio_iff {a b c D : ℚ} (hb : b ≠ 0) (hc : c ≠ 0) :
    IsSquare (D*a/(b*c)) ↔ IsSquare (D*a*b*c) := by
  constructor
  · intro h
    have hh := h.mul (IsSquare.sq (b*c))
    convert hh using 1 <;> field_simp
  · intro h
    have hh := h.div (IsSquare.sq (b*c))
    convert hh using 1 <;> field_simp

/-- Two factors in the same nonzero square class multiply to a square. -/
lemma same_class_product {a b N : ℚ} (hN : N ≠ 0)
    (ha : IsSquare (N*a)) (hb : IsSquare (N*b)) : IsSquare (a*b) := by
  have hh := (ha.mul hb).div (IsSquare.sq N)
  convert hh using 1 <;> field_simp

/-- The triangle-product criterion for two same-class pole distances and a
rational original edge. -/
lemma same_class_triangle {a b c N : ℚ} (hN : N ≠ 0)
    (ha : IsSquare a) (hb : IsSquare (N*b)) (hc : IsSquare (N*c)) :
    IsSquare (a*b*c) := by
  simpa only [mul_assoc] using ha.mul (same_class_product hN hb hc)

lemma rational_iff_square {r : ℝ} {q : ℚ} (hr : r^2 = (q : ℝ)) :
    r ∈ Set.range ((↑) : ℚ → ℝ) ↔ IsSquare q := by
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨s, ?_⟩
    apply Rat.cast_injective (α := ℝ)
    push_cast
    nlinarith [hr]
  · rintro ⟨s,hs⟩
    have he : r^2 = (s : ℝ)^2 := by rw [hs] at hr; simpa [pow_two] using hr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · exact ⟨s,h.symm⟩
    · exact ⟨-s,by simpa using h.symm⟩

section Inversion
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

lemma inversion_dist_sq (p x y : P) (hx : x ≠ p) (hy : y ≠ p) :
    dist (EuclideanGeometry.inversion p 1 x) (EuclideanGeometry.inversion p 1 y)^2 =
      dist x y ^ 2 / (dist x p ^ 2 * dist y p ^ 2) := by
  rw [EuclideanGeometry.dist_inversion_inversion hx hy]
  simp only [one_pow, mul_pow, div_pow]
  ring

/-- Only the triangle products of squared chords have to share a square class;
it is not necessary for the original squared chords themselves to do so. -/
lemma inversion_rational_iff (p x y : P) (hx : x ≠ p) (hy : y ≠ p)
    (a b c D : ℚ) (hD : 0 < D)
    (ha : dist x y ^ 2 = (a : ℝ))
    (hb : dist x p ^ 2 = (b : ℝ))
    (hc : dist y p ^ 2 = (c : ℝ)) :
    Real.sqrt (D : ℝ) *
        dist (EuclideanGeometry.inversion p 1 x) (EuclideanGeometry.inversion p 1 y)
      ∈ Set.range ((↑) : ℚ → ℝ) ↔ IsSquare (D*a*b*c) := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero] at hb
    exact hx (dist_eq_zero.mp (sq_eq_zero_iff.mp hb))
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero] at hc
    exact hy (dist_eq_zero.mp (sq_eq_zero_iff.mp hc))
  have hD0 : 0 ≤ (D : ℝ) := by exact_mod_cast hD.le
  have hs : (Real.sqrt (D : ℝ) *
        dist (EuclideanGeometry.inversion p 1 x) (EuclideanGeometry.inversion p 1 y))^2 =
      ((D*a/(b*c) : ℚ) : ℝ) := by
    rw [mul_pow,Real.sq_sqrt hD0,inversion_dist_sq p x y hx hy,ha,hb,hc]
    push_cast
    ring
  rw [rational_iff_square hs,square_ratio_iff hb0 hc0]

end Inversion
#print axioms same_class_triangle
#print axioms square_ratio_iff
#print axioms inversion_rational_iff
end Erdos213.SquareClassProjection
