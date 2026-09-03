import Submission.ThreefoldOrbits

/-! The natural multiplicative extension of two threefold orbits has three
additional median conditions. Their existence is not asserted here. -/
namespace Erdos213.ThreefoldPower
set_option maxHeartbeats 1000000

def norm (x y : ℚ) : ℚ := x^2+3*y^2

def minus (x y : ℚ) : Fin 3 → ℚ :=
  ![norm x y+1-2*x, norm x y+1+x-3*y, norm x y+1+x+3*y]

def plus (x y : ℚ) : Fin 3 → ℚ :=
  ![norm x y+1+2*x, norm x y+1-x+3*y, norm x y+1-x-3*y]

def squareRe (x y : ℚ) : ℚ := x^2-3*y^2
def squareIm (x y : ℚ) : ℚ := 2*x*y

def perm : Fin 3 → Fin 3 := ![0,2,1]

lemma perm_involutive : Function.Involutive perm := by
  intro i
  fin_cases i <;> rfl

lemma square_norm (x y : ℚ) :
    norm (squareRe x y) (squareIm x y)=norm x y^2 := by
  dsimp [norm,squareRe,squareIm]
  ring

lemma pair_factor (x y : ℚ) (i : Fin 3) :
    minus (squareRe x y) (squareIm x y) i = minus x y (perm i)*plus x y (perm i) := by
  fin_cases i <;> norm_num [minus,plus,perm,norm,squareRe,squareIm,Matrix.cons_val_two] <;> ring

lemma complementary_norms (x y : ℚ) (i : Fin 3) :
    plus x y i + minus x y i = 2*(norm x y+1) := by
  fin_cases i <;> norm_num [minus,plus,Matrix.cons_val_two] <;> ring

/-- These are the norm conditions for an orbit ratio t=x+y*sqrt(-3).
The factor 1/3 corresponds to scaling the physical orbit sqrt(-3)*t. -/
def Compatible (x y : ℚ) : Prop :=
  IsSquare (norm x y) ∧ ∀ i : Fin 3, IsSquare (minus x y i/3)

lemma cross_sum (x y : ℚ) :
    minus x y 0+minus x y 1+minus x y 2=3*(norm x y+1) := by
  norm_num [minus,Matrix.cons_val_two]
  ring

lemma cross_delta (x y : ℚ) :
    (minus x y 0)^2+(minus x y 1)^2+(minus x y 2)^2-
      minus x y 0*minus x y 1-minus x y 0*minus x y 2-
      minus x y 1*minus x y 2=9*norm x y := by
  norm_num [minus,norm,Matrix.cons_val_two]
  ring

lemma square_factor_iff (a b : ℚ) (ha : a≠0) : IsSquare (a^2*b) ↔ IsSquare b := by
  constructor
  · intro h
    have hh := h.div (IsSquare.sq a)
    have he : a^2*b/a^2=b := by field_simp
    rwa [he] at hh
  · exact fun h => (IsSquare.sq a).mul h

/-- A ratio compatible with its square must satisfy precisely the three new
plus-norm square conditions. Zero cross-distances are excluded explicitly. -/
theorem compatible_square_iff (x y : ℚ) (a : Fin 3 → ℚ)
    (ha : ∀ i, minus x y i=3*a i^2) (hne : ∀ i, a i≠0) :
    Compatible (squareRe x y) (squareIm x y) ↔ ∀ i, IsSquare (plus x y i) := by
  constructor
  · intro h i
    have hh := h.2 (perm i)
    rw [pair_factor,perm_involutive,ha] at hh
    have he : 3*a i^2*plus x y i/3=a i^2*plus x y i := by ring
    rw [he] at hh
    exact (square_factor_iff (a i) (plus x y i) (hne i)).mp hh
  · intro h
    refine ⟨?_,?_⟩
    · rw [square_norm]
      exact IsSquare.sq _
    · intro i
      rw [pair_factor,ha]
      have he : 3*a (perm i)^2*plus x y (perm i)/3=
          a (perm i)^2*plus x y (perm i) := by ring
      rw [he]
      exact (square_factor_iff _ _ (hne (perm i))).mpr (h (perm i))

/-- The cross-length triangle necessarily has square discriminant and area
square class three. This is not an existence theorem for such triangles. -/
lemma cross_triangle_invariants (x y r : ℚ) (a : Fin 3 → ℚ)
    (hr : norm x y=r^2) (ha : ∀ i, minus x y i=3*a i^2) :
    (a 0)^2+(a 1)^2+(a 2)^2=r^2+1 ∧
    ThreefoldOrbits.delta (a 0) (a 1) (a 2)=r^2 ∧
    3*(2*(a 0)^2*(a 1)^2+2*(a 0)^2*(a 2)^2+2*(a 1)^2*(a 2)^2-
      (a 0)^4-(a 1)^4-(a 2)^4)=(r^2-1)^2 := by
  have hs := cross_sum x y
  have hd := cross_delta x y
  rw [ha 0,ha 1,ha 2,hr] at hs hd
  have hs' : (a 0)^2+(a 1)^2+(a 2)^2=r^2+1 := by linarith
  have hd' : ThreefoldOrbits.delta (a 0) (a 1) (a 2)=r^2 := by
    dsimp [ThreefoldOrbits.delta]
    nlinarith only [hd]
  refine ⟨hs',hd',?_⟩
  dsimp [ThreefoldOrbits.delta] at hd'
  nlinarith only [sq_nonneg ((a 0)^2+(a 1)^2+(a 2)^2),
    congrArg (fun q : ℚ => q^2) hs',hd']

/-- The plus norms are exactly the opposite doubled-median squares. -/
lemma plus_eq_median (x y : ℚ) (a : Fin 3 → ℚ)
    (ha : ∀ i, minus x y i=3*a i^2) (i : Fin 3) :
    plus x y i=2*((a 0)^2+(a 1)^2+(a 2)^2)-3*a i^2 := by
  have hs := cross_sum x y
  rw [ha 0,ha 1,ha 2] at hs
  have hp := complementary_norms x y i
  rw [ha i] at hp
  linarith

theorem compatible_square_iff_medians (x y : ℚ) (a : Fin 3 → ℚ)
    (ha : ∀ i, minus x y i=3*a i^2) (hne : ∀ i, a i≠0) :
    Compatible (squareRe x y) (squareIm x y) ↔
      ∀ i, IsSquare (2*((a 0)^2+(a 1)^2+(a 2)^2)-3*a i^2) := by
  rw [compatible_square_iff x y a ha hne]
  simp only [plus_eq_median x y a ha]

/-- The known unequal-radius six-point source fails all three new median
conditions. Thus its square-ratio orbit is not an automatic extension. -/
lemma six_point_median_control :
    ¬IsSquare ((2*(392^2+645^2)-323^2 : ℚ)) ∧
    ¬IsSquare ((2*(323^2+645^2)-392^2 : ℚ)) ∧
    ¬IsSquare ((2*(323^2+392^2)-645^2 : ℚ)) := by
  norm_num

#print axioms pair_factor
#print axioms cross_triangle_invariants
#print axioms compatible_square_iff_medians
#print axioms six_point_median_control


/-- The precise normalized orbit ratio used by the known six-point source. -/
def knownRe : ℚ := 4631/22103
def knownIm : ℚ := 6776/22103

def knownCross : Fin 3 → ℚ := ![392/713,323/713,645/713]

lemma known_cross_equations (i : Fin 3) :
    minus knownRe knownIm i = 3 * knownCross i ^ 2 := by
  fin_cases i <;>
    norm_num [minus,norm,knownRe,knownIm,knownCross,Matrix.cons_val_two]

lemma known_cross_nonzero (i : Fin 3) : knownCross i ≠ 0 := by
  fin_cases i <;> norm_num [knownCross,Matrix.cons_val_two]

lemma known_ratio_compatible : Compatible knownRe knownIm := by
  constructor
  · refine ⟨407/713, ?_⟩
    norm_num [norm,knownRe,knownIm]
  · intro i
    rw [known_cross_equations]
    have he : 3 * knownCross i ^ 2 / 3 = knownCross i ^ 2 := by ring
    rw [he]
    exact IsSquare.sq _

/-- The failure is at the actual ratio, not just at an unnormalized list of
triangle side lengths. -/
lemma known_ratio_square_incompatible :
    ¬ Compatible (squareRe knownRe knownIm) (squareIm knownRe knownIm) := by
  intro h
  have hh := (compatible_square_iff knownRe knownIm knownCross
    known_cross_equations known_cross_nonzero).mp h 0
  have he : plus knownRe knownIm 0 = (1/713 : ℚ)^2 * 887044 := by
    norm_num [plus,norm,knownRe,knownIm]
  rw [he] at hh
  have hh' := (square_factor_iff (1/713) 887044 (by norm_num)).mp hh
  norm_num at hh'

/-- The circle branch supplies compatible power ratios, but all physical
orbits then share one circumcircle. It must not be counted as a GP witness. -/
lemma unit_circle_square_compatible (u v : ℚ) (hu : norm u v = 1) :
    Compatible (squareRe u v) (squareIm u v) := by
  have hnorm : norm (squareRe u v) (squareIm u v) = 1 := by
    rw [square_norm,hu]
    norm_num
  constructor
  · rw [hnorm]
    exact IsSquare.one
  · intro i
    fin_cases i
    · refine ⟨2*v, ?_⟩
      change (norm (squareRe u v) (squareIm u v)+1-2*squareRe u v)/3 = _
      rw [hnorm]
      dsimp [squareRe,norm] at *
      nlinarith only [hu]
    · refine ⟨u-v, ?_⟩
      change (norm (squareRe u v) (squareIm u v)+1+squareRe u v-3*squareIm u v)/3 = _
      rw [hnorm]
      dsimp [squareRe,squareIm,norm] at *
      nlinarith only [hu]
    · refine ⟨u+v, ?_⟩
      change (norm (squareRe u v) (squareIm u v)+1+squareRe u v+3*squareIm u v)/3 = _
      rw [hnorm]
      dsimp [squareRe,squareIm,norm] at *
      nlinarith only [hu]

#print axioms known_ratio_compatible
#print axioms known_ratio_square_incompatible
#print axioms unit_circle_square_compatible
end Erdos213.ThreefoldPower
