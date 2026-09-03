import Submission.CentralCircumcenters

/-! Reciprocal parameter changes preserve the central square conditions,
but the corresponding product octad is merely a similar, relabelled copy.
This is not an existence or nonexistence theorem for general configurations. -/
namespace Erdos213.CentralParameterSymmetry
open CentralCircumcenters
set_option maxHeartbeats 2000000

lemma radius_reciprocal (x y : ℚ) (hR : radiusSq x y ≠ 0) :
    radiusSq (x/radiusSq x y) (-y/radiusSq x y)=1/radiusSq x y := by
  dsimp [radiusSq] at hR ⊢
  field_simp

lemma tilt_reciprocal (x y : ℚ) (hy : y≠0) (hR : radiusSq x y ≠ 0) :
    tilt (x/radiusSq x y) (-y/radiusSq x y)=tilt x y := by
  simp only [tilt, radius_reciprocal x y hR]
  field_simp
  ring

lemma source_plus_reciprocal (x y : ℚ) (hR : radiusSq x y ≠ 0) :
    (x/radiusSq x y+1)^2+(-y/radiusSq x y)^2=
      ((x+1)^2+y^2)/radiusSq x y := by
  dsimp [radiusSq] at hR ⊢
  field_simp
  ring

lemma source_minus_reciprocal (x y : ℚ) (hR : radiusSq x y ≠ 0) :
    (x/radiusSq x y-1)^2+(-y/radiusSq x y)^2=
      ((x-1)^2+y^2)/radiusSq x y := by
  dsimp [radiusSq] at hR ⊢
  field_simp
  ring

lemma first_reciprocal (x y : ℚ) (hy : y≠0) (hR : radiusSq x y ≠ 0) :
    firstMissing (x/radiusSq x y) (-y/radiusSq x y)=
      secondMissing x y/radiusSq x y := by
  simp only [firstMissing, secondMissing, tilt_reciprocal x y hy hR,
    radius_reciprocal x y hR]
  field_simp
  ring

lemma second_reciprocal (x y : ℚ) (hy : y≠0) (hR : radiusSq x y ≠ 0) :
    secondMissing (x/radiusSq x y) (-y/radiusSq x y)=
      firstMissing x y/radiusSq x y := by
  simp only [firstMissing, secondMissing, tilt_reciprocal x y hy hR,
    radius_reciprocal x y hR]
  field_simp
  ring

def SquareInput (x y : ℚ) : Prop :=
  IsSquare (radiusSq x y) ∧ IsSquare ((x+1)^2+y^2) ∧
  IsSquare ((x-1)^2+y^2) ∧ IsSquare (firstMissing x y) ∧
  IsSquare (secondMissing x y)

lemma squareInput_reciprocal (x y : ℚ) (hy : y≠0) (hR : radiusSq x y ≠ 0)
    (h : SquareInput x y) : SquareInput (x/radiusSq x y) (-y/radiusSq x y) := by
  rcases h with ⟨hr,hp,hm,ha,hb⟩
  simp only [SquareInput, radius_reciprocal x y hR,
    source_plus_reciprocal x y hR, source_minus_reciprocal x y hR,
    first_reciprocal x y hy hR, second_reciprocal x y hy hR]
  exact ⟨IsSquare.one.div hr, hp.div hr, hm.div hr, hb.div hr, ha.div hr⟩

/-- The eight central coordinates are products of two opposite pairs. -/
def point {K : Type*} [CommRing K] (v w : K) : Fin 8 → K :=
  ![1,-1,v,-v,w,-w,w*v,-w*v]

def reciprocalIndex : Fin 8 → Fin 8 := ![2,3,0,1,6,7,4,5]

lemma reciprocalIndex_involution : Function.Involutive reciprocalIndex := by
  change ∀ i : Fin 8, reciprocalIndex (reciprocalIndex i)=i
  decide

lemma point_reciprocal {K : Type*} [Field K] (v w : K) (hv : v≠0) (i : Fin 8) :
    point v⁻¹ w i=point v w (reciprocalIndex i)/v := by
  fin_cases i <;> dsimp [point,reciprocalIndex]
  all_goals field_simp

lemma complex_reciprocal (x y : ℚ) :
    ((x/radiusSq x y : ℚ) : ℂ)+((-y/radiusSq x y : ℚ) : ℂ)*Complex.I=
      ((x : ℂ)+(y : ℂ)*Complex.I)⁻¹ := by
  have cast_via_real (q : ℚ) : (q : ℂ)=((q : ℝ) : ℂ) := by norm_cast
  simp only [cast_via_real]
  apply Complex.ext <;>
    simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, mul_one, add_zero, zero_add]
  all_goals simp [radiusSq, pow_two]

/-- The reciprocal source change is one uniform complex similarity, after
relabeling, rather than a new shape with improved general position. -/
lemma distance_reciprocal (v w : ℂ) (hv : v≠0) (i j : Fin 8) :
    dist (point v⁻¹ w i) (point v⁻¹ w j)=
      dist (point v w (reciprocalIndex i)) (point v w (reciprocalIndex j))/‖v‖ := by
  rw [point_reciprocal v w hv, point_reciprocal v w hv]
  simp only [dist_eq_norm, ← sub_div, norm_div]

lemma range_reciprocal {K : Type*} [Field K] (v w : K) (hv : v≠0) :
    Set.range (point v⁻¹ w)=(fun z => z/v) '' Set.range (point v w) := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨point v w (reciprocalIndex i), ⟨_,rfl⟩, (point_reciprocal v w hv i).symm⟩
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    refine ⟨reciprocalIndex i,?_⟩
    rw [point_reciprocal v w hv, reciprocalIndex_involution]

lemma axis_preserved (x y : ℚ) (hx : x=0) : x/radiusSq x y=0 := by
  simp [hx]

#print axioms squareInput_reciprocal
#print axioms complex_reciprocal
#print axioms distance_reciprocal
#print axioms range_reciprocal
end Erdos213.CentralParameterSymmetry
