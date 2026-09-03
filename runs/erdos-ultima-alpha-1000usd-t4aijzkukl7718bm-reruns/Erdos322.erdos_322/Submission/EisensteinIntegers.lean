import FormalConjecturesUtil

/-! Explicit Eisenstein integers and their norm-Euclidean structure. -/
namespace Erdos322Research.EisensteinIntegers
open QuadraticAlgebra
abbrev E := QuadraticAlgebra ℤ (-1) (-1)

lemma norm_formula (z : E) : z.norm = z.re^2-z.re*z.im+z.im^2 := by
  simp only [QuadraticAlgebra.norm_def]
  ring

lemma norm_nonneg (z : E) : 0 ≤ z.norm := by
  rw [norm_formula]
  nlinarith [sq_nonneg z.re,sq_nonneg z.im,sq_nonneg (z.re-z.im)]

lemma norm_eq_zero {z : E} : z.norm=0 ↔ z=0 := by
  constructor
  · intro h
    rw [norm_formula] at h
    have hr : z.re=0 := by nlinarith [sq_nonneg z.re,sq_nonneg z.im,sq_nonneg (z.re-z.im)]
    have hi : z.im=0 := by nlinarith [sq_nonneg z.re,sq_nonneg z.im,sq_nonneg (z.re-z.im)]
    ext <;> assumption
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

lemma norm_pos {z : E} : 0 < z.norm ↔ z≠0 := by
  constructor
  · intro h hz
    subst z
    simp at h
  · intro hz
    have hn : z.norm≠0 := norm_eq_zero.not.mpr hz
    have h := norm_nonneg z
    omega

lemma norm_eq_one_iff {z : E} : z.norm=1 ↔ IsUnit z := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit,Int.isUnit_iff]
  have h := norm_nonneg z
  omega

noncomputable def quotient (x y : E) : E :=
  ⟨round (((x*star y).re : ℚ)/y.norm),round (((x*star y).im : ℚ)/y.norm)⟩

noncomputable def remainder (x y : E) : E := x-y*quotient x y

lemma quotient_zero (x : E) : quotient x 0=0 := by
  ext <;> simp [quotient]

private lemma round_error (a N : ℤ) (hN : 0 < N) :
    4*(a-N*round ((a : ℚ)/N))^2 ≤ N^2 := by
  have hNR : (0 : ℚ) < N := by exact_mod_cast hN
  have hh := abs_sub_round ((a : ℚ)/N)
  have hl := (abs_le.mp hh).1
  have hu := (abs_le.mp hh).2
  have hlo : -(N : ℚ)/2 ≤ a-N*round ((a : ℚ)/N) := by
    have h := mul_le_mul_of_nonneg_left hl hNR.le
    field_simp at h ⊢
    nlinarith
  have hup : (a : ℚ)-N*round ((a : ℚ)/N) ≤ N/2 := by
    have h := mul_le_mul_of_nonneg_left hu hNR.le
    field_simp at h ⊢
    nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr hup) (sub_nonneg.mpr hlo)
  have h : 4*((a : ℚ)-N*round ((a : ℚ)/N))^2 ≤ (N : ℚ)^2 := by nlinarith
  exact_mod_cast h

lemma remainder_norm_lt (x : E) {y : E} (hy : y≠0) :
    (remainder x y).norm < y.norm := by
  have hN := norm_pos.mpr hy
  let u := x*star y
  let v := u-(y.norm : E)*quotient x y
  have hv : v=remainder x y*star y := by
    dsimp [v,u,remainder]
    rw [show (y.norm : E)=y*star y from QuadraticAlgebra.algebraMap_norm_eq_mul_star y]
    ring
  have hnorm : v.norm=(remainder x y).norm*y.norm := by
    rw [hv,map_mul,QuadraticAlgebra.norm_star]
  have hr : 4*v.re^2 ≤ y.norm^2 := by
    simpa [v,u,quotient] using round_error (x*star y).re y.norm hN
  have hi : 4*v.im^2 ≤ y.norm^2 := by
    simpa [v,u,quotient] using round_error (x*star y).im y.norm hN
  have hbound : 4*v.norm ≤ 3*y.norm^2 := by
    rw [norm_formula]
    nlinarith [sq_nonneg (v.re+v.im)]
  rw [hnorm] at hbound
  nlinarith

lemma natAbs_remainder_norm_lt (x : E) {y : E} (hy : y≠0) :
    (remainder x y).norm.natAbs < y.norm.natAbs := by
  have h := remainder_norm_lt x hy
  have h1 := norm_nonneg (remainder x y)
  have h2 := norm_nonneg y
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h

lemma norm_mul_ge (x y : E) (hy : y≠0) :
    x.norm.natAbs ≤ (x*y).norm.natAbs := by
  rw [map_mul,Int.natAbs_mul]
  apply Nat.le_mul_of_pos_right
  exact Int.natAbs_pos.mpr (ne_of_gt (norm_pos.mpr hy))

noncomputable instance : EuclideanDomain E where
  quotient := quotient
  remainder := remainder
  quotient_zero := quotient_zero
  quotient_mul_add_remainder_eq a b := by simp only [remainder]; ring
  r := fun a b ↦ a.norm.natAbs < b.norm.natAbs
  r_wellFounded := (measure (fun a : E ↦ a.norm.natAbs)).wf
  remainder_lt := natAbs_remainder_norm_lt
  mul_left_not_lt a b hb := not_lt_of_ge (norm_mul_ge a b hb)

end Erdos322Research.EisensteinIntegers
