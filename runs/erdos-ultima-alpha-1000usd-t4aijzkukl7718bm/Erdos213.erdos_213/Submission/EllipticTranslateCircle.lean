import Submission.EllipticTranslate
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! The exceptional symbolic-square branch of the elliptic translation
construction is a circle. Individual nonexceptional rational points can
still satisfy the distance equations; they are not excluded by this file. -/
namespace Erdos213.EllipticTranslate
noncomputable section
set_option maxHeartbeats 3000000

def doubleYFactor (A B s : ℚ) : ℚ :=
  -1+(3*s^2+A)*(s-doubleX A B s)/(2*value A B s)

lemma double_on_curve (A B s : ℚ) (hs : value A B s ≠ 0) :
    value A B (doubleX A B s) = value A B s*(doubleYFactor A B s)^2 := by
  have aux (k c : ℚ)
      (hd : (3*s^2+A)^2=4*value A B s*(k+2*s))
      (hc : 2*value A B s*c=(3*s^2+A)*(s-k)-2*value A B s) :
      value A B k=value A B s*c^2 := by
    have hh : 4*value A B s*(value A B k-value A B s*c^2)=0 := by
      dsimp only [value] at *
      linear_combination -(s-k)^2*hd-
        (2*(s^3+A*s+B)*c+(3*s^2+A)*(s-k)-2*(s^3+A*s+B))*hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
      (mul_ne_zero (by norm_num) hs))
  refine aux (doubleX A B s) (doubleYFactor A B s) ?_ ?_
  · dsimp [doubleX]
    field_simp
    ring
  · unfold doubleYFactor
    field_simp
    ring

/-- When the imaginary translation doubles to two-torsion, the short
Weierstrass coefficients have this explicit quarter-point form. -/
lemma circle_coefficients (A B s : ℚ) (hs : value A B s ≠ 0)
    (hk : value A B (doubleX A B s) = 0) :
    A = s^2-2*s*doubleX A B s-2*(doubleX A B s)^2 ∧
    B = -(doubleX A B s)^3-A*doubleX A B s := by
  let k := doubleX A B s
  have hY : doubleYFactor A B s = 0 := by
    have hh := double_on_curve A B s hs
    rw [hk] at hh
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh.symm).resolve_left hs)
  have hM : (3*s^2+A)*(s-k)=2*value A B s := by
    dsimp [doubleYFactor] at hY
    have hden : 2*value A B s ≠ 0 := mul_ne_zero (by norm_num) hs
    have hh : (3*s^2+A)*(s-k)/(2*value A B s)=1 := by
      change -1+(3*s^2+A)*(s-k)/(2*value A B s)=0 at hY
      linarith
    exact (div_eq_one_iff_eq hden).mp hh
  have hM0 : 3*s^2+A ≠ 0 := by
    intro h0
    rw [h0,zero_mul] at hM
    exact hs (by linarith)
  have hd : (3*s^2+A)^2=4*value A B s*(k+2*s) := by
    dsimp [k,doubleX]
    field_simp
    ring
  have hf : (3*s^2+A)*((3*s^2+A)-2*(s-k)*(k+2*s))=0 := by
    linear_combination hd-2*(k+2*s)*hM
  have hf' := (mul_eq_zero.mp hf).resolve_left hM0
  constructor
  · change A=s^2-2*s*k-2*k^2
    nlinarith only [hf']
  · dsimp [value] at hk
    linarith

lemma circle_norm (A B s u v : ℚ) (hs : value A B s ≠ 0) (hus : u ≠ s)
    (hu : v^2=value A B u) (hk : value A B (doubleX A B s) = 0) :
    (realPart A B s u-doubleX A B s)^2-value A B s*(imagCoeff s u v)^2 =
      (s-doubleX A B s)^2 := by
  obtain ⟨hA,hB⟩ := circle_coefficients A B s hs hk
  let k := doubleX A B s
  have hA' : A=s^2-2*s*k-2*k^2 := hA
  have hB' : B= -k^3-(s^2-2*s*k-2*k^2)*k := by rw [← hA']; exact hB
  have hH : value A B s=(s-k)^2*(2*s+k) := by
    dsimp [value]
    rw [hA',hB']
    ring
  have hu' : v^2=u^3+(s^2-2*s*k-2*k^2)*u-k^3-(s^2-2*s*k-2*k^2)*k := by
    rw [hu]
    dsimp [value]
    rw [hA',hB']
    ring
  change (realPart A B s u-k)^2-value A B s*(imagCoeff s u v)^2=(s-k)^2
  dsimp [realPart,imagCoeff,numerator]
  have hus' := sub_ne_zero.mpr hus
  field_simp
  rw [hH,hA',hB']
  linear_combination -4*(s-k)^2*(2*s+k)*hu'

def center (A B s k : ℚ) : ℂ :=
  ⟨(k : ℝ)/Real.sqrt (-((value A B s : ℚ) : ℝ)),0⟩

lemma center_dist_sq (A B s u v k : ℚ) (hs : value A B s < 0) :
    dist (point A B s u v) (center A B s k)^2 =
      ((((realPart A B s u-k)^2-value A B s*(imagCoeff s u v)^2)/
        (-value A B s) : ℚ) : ℝ) := by
  have hsR : ((value A B s : ℚ) : ℝ) < 0 := by exact_mod_cast hs
  have hroot : Real.sqrt (-((value A B s : ℚ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hroot2 := Real.sq_sqrt (show 0 ≤ -((value A B s : ℚ) : ℝ) by linarith)
  have hs0 := ne_of_lt hsR
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [point,center,Complex.sub_re,Complex.sub_im,sub_zero]
  push_cast
  field_simp
  linear_combination ((realPart A B s u : ℝ)-(k : ℝ))^2*hroot2

/-- The only branch that makes the generic duplication square is cospherical
for EVERY set of rational source points where the formula is defined. -/
theorem symbolic_square_cospherical {ι : Type*} (A B s : ℚ) (u v : ι → ℚ)
    (hs : value A B s < 0) (hus : ∀ i, u i ≠ s)
    (hu : ∀ i, v i^2=value A B (u i))
    (hsquare : IsSquare (algebraMap EllipticDuplication.F (EllipticDuplication.E A B)
      (EllipticDuplication.lift (EllipticDuplication.quartic A B (doubleX A B s))/
        (4*EllipticDuplication.lift (EllipticDuplication.cubic A B))))) :
    EuclideanGeometry.Cospherical (Set.range (fun i => point A B s (u i) (v i))) := by
  have hk : value A B (doubleX A B s)=0 :=
    (EllipticDuplication.elliptic_square_iff A B (doubleX A B s)).mp hsquare
  let q : ℚ := (s-doubleX A B s)^2/(-value A B s)
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) (by linarith)
  refine ⟨center A B s (doubleX A B s),Real.sqrt (q : ℝ),?_⟩
  rintro _ ⟨i,rfl⟩
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by exact_mod_cast hq),center_dist_sq _ _ _ _ _ _ hs,
    circle_norm A B s (u i) (v i) (ne_of_lt hs) (hus i) (hu i) hk]

/-- The endpoint corresponding to the rational elliptic identity O. -/
lemma origin_norm (A B s u v : ℚ) (hs : value A B s ≠ 0) (hus : u ≠ s)
    (hu : v^2=value A B u) :
    ((realPart A B s u-s)^2-value A B s*(imagCoeff s u v)^2)/(-value A B s) =
      (2/(u-s))^2*(u-doubleX A B s) := by
  have hid : (numerator A B s u-s*(u-s)^2)^2-4*value A B s*v^2 =
      ((3*s^2+A)^2-4*value A B s*(u+2*s))*(u-s)^2 := by
    dsimp [numerator,value] at *
    linear_combination -4*(s^3+A*s+B)*hu
  have hus' := sub_ne_zero.mpr hus
  dsimp [realPart,imagCoeff,doubleX]
  field_simp
  linear_combination -4*hid

lemma origin_distance_iff (A B s u v : ℚ) (hs : value A B s < 0)
    (hus : u ≠ s) (hu : v^2=value A B u) :
    dist (point A B s u v) (center A B s s) ∈ Set.range ((↑) : ℚ → ℝ) ↔
      IsSquare (u-doubleX A B s) := by
  rw [rational_of_sq dist_nonneg (center_dist_sq _ _ _ _ _ _ hs),
    origin_norm A B s u v (ne_of_lt hs) hus hu]
  exact square_mul_sq_iff _ _ (div_ne_zero (by norm_num) (sub_ne_zero.mpr hus))

#print axioms double_on_curve
#print axioms circle_coefficients
#print axioms circle_norm
#print axioms symbolic_square_cospherical
#print axioms origin_distance_iff
end
end Erdos213.EllipticTranslate
