import Submission.EllipticDuplication
import Mathlib.Analysis.Complex.Basic

/-! Distances in a translated elliptic x-projection. These formulas reduce
the proposed construction to new square conditions at sums of rational
points; they do not supply an arbitrary-cardinality configuration. -/
namespace Erdos213.EllipticTranslate
noncomputable section
set_option maxHeartbeats 3000000

def value {R : Type*} [CommRing R] (A B t : R) : R := t^3+A*t+B

def numerator {R : Type*} [CommRing R] (A B s u : R) : R :=
  (u+s)*(u*s+A)+2*B

def realPart (A B s u : ℚ) : ℚ := numerator A B s u/(u-s)^2

def imagCoeff (s u v : ℚ) : ℚ := -2*v/(u-s)^2

def doubleX (A B s : ℚ) : ℚ := (3*s^2+A)^2/(4*value A B s)-2*s

def sumX (u v r w : ℚ) : ℚ := (v-w)^2/(u-r)^2-u-r

def normDiff (A B s u v r w : ℚ) : ℚ :=
  (realPart A B s u-realPart A B s r)^2 -
    value A B s*(imagCoeff s u v-imagCoeff s r w)^2

/-- Denominator-free norm identity, valid over any commutative ring. -/
lemma norm_identity {R : Type*} [CommRing R] (A B s u v r w H : R)
    (hu : v^2=value A B u) (hr : w^2=value A B r) (hs : H=value A B s) :
    (numerator A B s u*(r-s)^2-numerator A B s r*(u-s)^2)^2 -
        4*H*(v*(r-s)^2-w*(u-s)^2)^2 =
      ((u-r)^2*((3*s^2+A)^2+4*H*(u+r-2*s))-4*H*(v-w)^2)*
        (u-s)^2*(r-s)^2 := by
  dsimp [numerator,value] at *
  linear_combination
    4*H*(r-s)^2*(u-r)*(u+r-2*s)*hu -
    4*H*(u-s)^2*(u-r)*(u+r-2*s)*hr +
    4*(r-u)^2*(r-2*s+u)*(-A*r*u+A*s^2-B*r+2*B*s-B*u+
      2*r*s^3-3*r*s^2*u-s^4+2*s^3*u)*hs

/-- After scaling the plane by 1/sqrt(-f(s)), the square class of a chord
is exactly the square class of x(R+T)-x(2S), whenever x(R) != x(T). -/
lemma norm_sum_identity (A B s u v r w : ℚ)
    (hu : v^2=value A B u) (hr : w^2=value A B r)
    (hs : value A B s ≠ 0) (hus : u ≠ s) (hrs : r ≠ s) (hur : u ≠ r) :
    normDiff A B s u v r w / (-value A B s) =
      (2*(u-r)/((u-s)*(r-s)))^2 * (sumX u v r w-doubleX A B s) := by
  have hid := norm_identity A B s u v r w (value A B s) hu hr rfl
  have hus' := sub_ne_zero.mpr hus
  have hrs' := sub_ne_zero.mpr hrs
  have hur' := sub_ne_zero.mpr hur
  dsimp [normDiff,realPart,imagCoeff,sumX,doubleX]
  field_simp
  linear_combination -4*hid

lemma square_mul_sq_iff (a b : ℚ) (ha : a ≠ 0) :
    IsSquare (a^2*b) ↔ IsSquare b := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r/a,?_⟩
    field_simp
    nlinarith only [hr]
  · intro h
    exact (IsSquare.sq _).mul h

lemma square_norm_iff (A B s u v r w : ℚ)
    (hu : v^2=value A B u) (hr : w^2=value A B r)
    (hs : value A B s ≠ 0) (hus : u ≠ s) (hrs : r ≠ s) (hur : u ≠ r) :
    IsSquare (normDiff A B s u v r w / (-value A B s)) ↔
      IsSquare (sumX u v r w-doubleX A B s) := by
  rw [norm_sum_identity A B s u v r w hu hr hs hus hrs hur]
  exact square_mul_sq_iff _ _ (div_ne_zero
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hur))
    (mul_ne_zero (sub_ne_zero.mpr hus) (sub_ne_zero.mpr hrs)))

/-- Coordinates of the actual normalized complex point. The original
imaginary translation is by (s,sqrt(f(s))) on the elliptic curve; f(s)<0. -/
def point (A B s u v : ℚ) : ℂ :=
  ⟨(realPart A B s u : ℝ)/Real.sqrt (-((value A B s : ℚ) : ℝ)),(imagCoeff s u v : ℝ)⟩

lemma point_dist_sq (A B s u v r w : ℚ) (hs : value A B s < 0) :
    dist (point A B s u v) (point A B s r w)^2 =
      ((normDiff A B s u v r w / (-value A B s) : ℚ) : ℝ) := by
  have hsR : ((value A B s : ℚ) : ℝ) < 0 := by exact_mod_cast hs
  have hroot : Real.sqrt (-((value A B s : ℚ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hroot2 := Real.sq_sqrt (show 0 ≤ -((value A B s : ℚ) : ℝ) by linarith)
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [point,Complex.sub_re,Complex.sub_im,normDiff]
  push_cast
  have hs0 : ((value A B s : ℚ) : ℝ) ≠ 0 := ne_of_lt hsR
  field_simp
  linear_combination
    ((realPart A B s u : ℝ)-(realPart A B s r : ℝ))^2*hroot2

lemma rational_of_sq {d : ℝ} {q : ℚ} (hd : 0 ≤ d) (he : d^2=(q : ℝ)) :
    d ∈ Set.range ((↑) : ℚ → ℝ) ↔ IsSquare q := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have hh : (q : ℝ)=(r : ℝ)*(r : ℝ) := by rw [← he,hr,pow_two]
    exact_mod_cast hh
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    have hsq : d^2=(r : ℝ)^2 := by rw [he,hr]; push_cast; ring
    rw [Rat.cast_abs]
    exact (sq_eq_sq₀ (abs_nonneg _) hd).mp (by simpa only [sq_abs] using hsq.symm)

/-- Exact rational-distance criterion, including the positive real scaling
and the complex Euclidean metric. -/
theorem distance_iff (A B s u v r w : ℚ)
    (hu : v^2=value A B u) (hr : w^2=value A B r)
    (hs : value A B s < 0) (hus : u ≠ s) (hrs : r ≠ s) (hur : u ≠ r) :
    dist (point A B s u v) (point A B s r w) ∈ Set.range ((↑) : ℚ → ℝ) ↔
      IsSquare (sumX u v r w-doubleX A B s) := by
  rw [rational_of_sq dist_nonneg (point_dist_sq A B s u v r w hs)]
  exact square_norm_iff A B s u v r w hu hr (ne_of_lt hs) hus hrs hur

lemma on_curve_ne_source (A B s u v : ℚ) (hs : value A B s < 0)
    (hu : v^2=value A B u) : u ≠ s := by
  intro h
  rw [h] at hu
  nlinarith [sq_nonneg v]

lemma same_x_rational (A B s u v w : ℚ) (hs : value A B s < 0) :
    dist (point A B s u v) (point A B s u w) ∈ Set.range ((↑) : ℚ → ℝ) := by
  rw [rational_of_sq dist_nonneg (point_dist_sq A B s u v u w hs)]
  refine ⟨imagCoeff s u v-imagCoeff s u w,?_⟩
  have hs0 := ne_of_lt hs
  dsimp [normDiff]
  field_simp
  ring

/-- Complete indexed criterion, including equal-x and self-pair cases.
The source nonvanishing denominators follow from the negative cubic value
and the rational on-curve equations, rather than being assumed here. -/
theorem all_distances_iff {ι : Type*} (A B s : ℚ) (u v : ι → ℚ)
    (hs : value A B s < 0) (hu : ∀ i, v i^2=value A B (u i)) :
    (∀ i j, dist (point A B s (u i) (v i)) (point A B s (u j) (v j)) ∈
      Set.range ((↑) : ℚ → ℝ)) ↔
    (∀ i j, u i ≠ u j → IsSquare (sumX (u i) (v i) (u j) (v j)-doubleX A B s)) := by
  have hden (i) := on_curve_ne_source A B s (u i) (v i) hs (hu i)
  constructor
  · intro hd i j hij
    exact (distance_iff A B s (u i) (v i) (u j) (v j)
      (hu i) (hu j) hs (hden i) (hden j) hij).mp (hd i j)
  · intro hq i j
    by_cases hij : u i=u j
    · rw [hij]
      exact same_x_rational A B s (u j) (v i) (v j) hs
    · exact (distance_iff A B s (u i) (v i) (u j) (v j)
        (hu i) (hu j) hs (hden i) (hden j) hij).mpr (hq i j hij)

/-- Opposite rational points are a separate case: their normalized chord
is vertical and is always rational. No division by x(R)-x(-R) is used. -/
lemma opposite_distance (A B s u v : ℚ) :
    dist (point A B s u v) (point A B s u (-v)) =
      ((|4*v/(u-s)^2| : ℚ) : ℝ) := by
  rw [dist_eq_norm,Complex.norm_def]
  simp only [point,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,sub_self,
    zero_mul,zero_add]
  rw [Real.sqrt_mul_self_eq_abs]
  push_cast
  rw [show (imagCoeff s u v : ℝ)-(imagCoeff s u (-v) : ℝ) =
    -((4*v/(u-s)^2 : ℚ) : ℝ) by simp [imagCoeff]; push_cast; ring]
  rw [abs_neg]
  push_cast
  rfl

#print axioms norm_identity
#print axioms norm_sum_identity
#print axioms square_norm_iff
#print axioms point_dist_sq
#print axioms distance_iff
#print axioms opposite_distance
#print axioms all_distances_iff
end
end Erdos213.EllipticTranslate
