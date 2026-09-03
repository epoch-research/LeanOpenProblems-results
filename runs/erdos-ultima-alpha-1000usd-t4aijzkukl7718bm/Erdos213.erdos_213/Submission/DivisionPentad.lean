import Submission.EndpointSwitching
import Submission.RationalGaussian
import Submission.DivisionCuboid

/-! An end-to-end necessary norm condition for five selected four-division
y-coordinates, allowing arbitrary positive real endpoint weights. -/
namespace Erdos213.DivisionPentad
open RationalGaussian EndpointSwitching
set_option maxHeartbeats 2000000

/-- Indices 0,1,2,4,9 in the twelve-point signed four-division catalog. -/
def points (z w : G) : Fin 5 → G :=
  ![ii*z*(z-1), -ii*z*(z-1), ii*z*(z+1), w*(1+w), -ii*w*(z^2+ii*z*w)]

def cycle {ι : Type*} (p : ι → G) (a b c d : ι) : G :=
  ((p a-p b)*(p c-p d))/((p b-p c)*(p d-p a))

lemma cycle_den_ne {ι : Type*} {p : ι → G} (hp : Function.Injective p)
    {a b c d : ι} (hbc : b ≠ c) (hda : d ≠ a) :
    (p b-p c)*(p d-p a) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr (hp.ne hbc)) (sub_ne_zero.mpr (hp.ne hda))

private lemma ii_pow3 : ii^3 = -ii := by rw [pow_succ,ii_sq]; ring
private lemma ii_pow4 : ii^4 = 1 := by rw [show (4 : ℕ)=2*2 by rfl,pow_mul,ii_sq]; ring
private lemma ii_pow5 : ii^5 = ii := by rw [pow_succ,ii_pow4,one_mul]
private lemma ii_pow6 : ii^6 = -1 := by rw [show (6 : ℕ)=2*3 by rfl,pow_mul,ii_sq]; ring

lemma z_identity (z w : G) (hzw : z^2+w^2=1) (hz : z ≠ 0)
    (hp : Function.Injective (points z w)) :
    cycle (points z w) 0 1 2 4 * cycle (points z w) 0 1 3 2 = ii*w^2/z := by
  unfold cycle
  rw [div_mul_div_comm]
  apply (div_eq_div_iff
    (mul_ne_zero (cycle_den_ne hp (by decide) (by decide))
      (cycle_den_ne hp (by decide) (by decide))) hz).mpr
  simp only [points, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (norm := skip)
    (-4*z^4*(-ii*w^4-w^3*z-ii*w^3+ii*w^2*z^2-w^2*z-ii*w^2+
      w*z^3-w*z^2+ii*w*z-ii*w+z^3-z))*hzw
  ring_nf
  simp only [ii_pow3,ii_pow4,ii_pow5,ii_pow6]
  ring

lemma w_identity (z w : G) (hzw : z^2+w^2=1) (hz : z ≠ 0)
    (hp : Function.Injective (points z w)) :
    cycle (points z w) 0 1 2 3 * cycle (points z w) 0 2 1 4 = ii*w/z^2 := by
  unfold cycle
  rw [div_mul_div_comm]
  apply (div_eq_div_iff
    (mul_ne_zero (cycle_den_ne hp (by decide) (by decide))
      (cycle_den_ne hp (by decide) (by decide))) (pow_ne_zero _ hz)).mpr
  simp only [points, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (norm := skip)
    (-4*z^5*(ii*w^3+w^2*(1+ii)+w*z^2-ii*w*z+ii*w-z^2+z))*hzw
  ring_nf
  simp only [ii_pow3,ii_pow4,ii_pow5,ii_pow6]
  ring

lemma cycle_square {ι : Type*} (p : ι → G) (hp : Function.Injective p)
    (h : RealWeightedRational (fun i j => norm (p i-p j)))
    {a b c d : ι} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    IsSquare (norm (cycle p a b c d)) := by
  simp only [cycle,map_div₀,map_mul]
  exact four_edge_square _ h hab hbc hcd hda
    (norm_ne_zero (sub_ne_zero.mpr (hp.ne hbc)))
    (norm_ne_zero (sub_ne_zero.mpr (hp.ne hda)))

/-- If the five points can be endpoint-reweighted to rational lengths, both
complex parameters have rational norms. The weights need not be rational. -/
theorem norm_squares_of_weighted (z w : G) (hzw : z^2+w^2=1)
    (hz : z ≠ 0) (hw : w ≠ 0) (hp : Function.Injective (points z w))
    (h : RealWeightedRational (fun i j => norm (points z w i-points z w j))) :
    IsSquare (norm z) ∧ IsSquare (norm w) := by
  have h1 := (cycle_square _ hp h (a:=0) (b:=1) (c:=2) (d:=4)
    (by decide) (by decide) (by decide) (by decide)).mul
    (cycle_square _ hp h (a:=0) (b:=1) (c:=3) (d:=2)
      (by decide) (by decide) (by decide) (by decide))
  have h2 := (cycle_square _ hp h (a:=0) (b:=1) (c:=2) (d:=3)
    (by decide) (by decide) (by decide) (by decide)).mul
    (cycle_square _ hp h (a:=0) (b:=2) (c:=1) (d:=4)
      (by decide) (by decide) (by decide) (by decide))
  rw [← map_mul,z_identity z w hzw hz hp,map_div₀,map_mul,map_pow,norm_ii,one_mul] at h1
  rw [← map_mul,w_identity z w hzw hz hp,map_div₀,map_mul,map_pow,norm_ii,one_mul] at h2
  have hnz := norm_ne_zero hz
  have hnw := norm_ne_zero hw
  constructor
  · convert (IsSquare.sq (norm w)).div h1 using 1
    field_simp
  · convert h2.mul (IsSquare.sq (norm z)) using 1
    field_simp

/-- Actual real weights on complex distances imply the algebraic square
criterion above. No rationality assumption is imposed on those weights. -/
lemma weighted_of_lengths {ι : Type*} (p : ι → G) (l : ι → ℝ)
    (hl : ∀ i, 0 < l i)
    (h : ∀ i j, i ≠ j → l i*l j*dist (toComplex (p i)) (toComplex (p j))
      ∈ Set.range ((↑) : ℚ → ℝ)) :
    RealWeightedRational (fun i j => norm (p i-p j)) := by
  refine ⟨fun i => l i^2,fun i => sq_pos_of_pos (hl i),?_⟩
  intro i j hij
  obtain ⟨r,hr⟩ := h i j hij
  refine ⟨r,?_⟩
  rw [hr,mul_pow,mul_pow,dist_sq]

open DivisionCuboid in
/-- The explicit Joukowski-coordinate pentad. -/
def parameterPoints (x y : ℚ) : Fin 5 → G :=
  points ⟨zRe x y,zIm x y⟩ ⟨wRe x y,wIm x y⟩

open DivisionCuboid in
/-- This restricted five-point construction, even with arbitrary real endpoint
weights, would require a positive rational perfect cuboid off the exceptional
axes and unit circle. This is only a necessary condition. -/
theorem perfectCuboid_of_weighted_lengths (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : radiusSq x y ≠ 1) (hp : Function.Injective (parameterPoints x y))
    (l : Fin 5 → ℝ) (hl : ∀ i, 0 < l i)
    (hd : ∀ i j, i ≠ j → l i*l j*
      dist (toComplex (parameterPoints x y i)) (toComplex (parameterPoints x y j))
      ∈ Set.range ((↑) : ℚ → ℝ)) : RationalPerfectCuboid := by
  have hspos : 0 < radiusSq x y := by dsimp [radiusSq]; positivity
  have hs0 := ne_of_gt hspos
  have hs1 : radiusSq x y+1 ≠ 0 := by linarith
  let z : G := ⟨zRe x y,zIm x y⟩
  let w : G := ⟨wRe x y,wIm x y⟩
  have hzw : z^2+w^2=1 := by
    apply toComplex_injective
    simp only [map_add,map_pow,map_one]
    exact complex_pythagorean x y hs0
  have hz : z ≠ 0 := by
    intro h
    have he := congrArg QuadraticAlgebra.re h
    change zRe x y=0 at he
    exact (div_ne_zero (mul_ne_zero hx hs1) (mul_ne_zero (by norm_num) hs0)) he
  have hw : w ≠ 0 := by
    intro h
    have he := congrArg QuadraticAlgebra.re h
    change wRe x y=0 at he
    exact (div_ne_zero (mul_ne_zero hy hs1) (mul_ne_zero (by norm_num) hs0)) he
  obtain ⟨hzsq,hwsq⟩ := norm_squares_of_weighted z w hzw hz hw hp
    (weighted_of_lengths (parameterPoints x y) l hl hd)
  have hnz : norm z = normZ x y := by
    rw [RationalGaussian.norm_components]
    exact (DivisionCuboid.norm_components x y hs0).1
  have hnw : norm w = normW x y := by
    rw [RationalGaussian.norm_components]
    exact (DivisionCuboid.norm_components x y hs0).2
  exact perfectCuboid_of_norms x y hx hy hs (hnz ▸ hzsq) (hnw ▸ hwsq)

/-- Inversion followed by any positive real dilation is a special case of
endpoint reweighting; the inversion center need not be rational. -/
lemma weighted_of_inverted_lengths {ι : Type*} (p : ι → G) (o : ℂ)
    (ho : ∀ i, toComplex (p i) ≠ o) (A : ℝ) (hA : 0 < A)
    (hd : ∀ i j, i ≠ j → A*
      dist (EuclideanGeometry.inversion o 1 (toComplex (p i)))
        (EuclideanGeometry.inversion o 1 (toComplex (p j)))
      ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ l : ι → ℝ, (∀ i, 0 < l i) ∧
      ∀ i j, i ≠ j → l i*l j*dist (toComplex (p i)) (toComplex (p j))
        ∈ Set.range ((↑) : ℚ → ℝ) := by
  exact weights_of_inverted_lengths (fun i => toComplex (p i)) o ho A hA hd

#print axioms norm_squares_of_weighted
#print axioms weighted_of_lengths
#print axioms perfectCuboid_of_weighted_lengths
#print axioms weighted_of_inverted_lengths
end Erdos213.DivisionPentad
