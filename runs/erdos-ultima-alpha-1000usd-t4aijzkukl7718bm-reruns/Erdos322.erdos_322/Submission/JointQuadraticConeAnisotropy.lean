import Submission.QuadraticSpecializationAnisotropy
import Submission.JointQuadraticGaussianInterpolation

/-! Arbitrary-degree fourth-power anisotropy of the coordinate algebra of
the explicit common quadratic cone. The two quadratic roots are treated
simultaneously by a separating four-branch formal specialization. -/
namespace Erdos322Research.JointQuadraticCone

noncomputable section
open QuarticFormalSpecialization QuadraticSpecializationAnisotropy
open JointQuadraticGaussianInterpolation (imag imag_sq imag_ne_zero)
set_option Elab.async false
set_option maxHeartbeats 0

abbrev K := GaussianQuartic.GaussianRational
abbrev Base := MvPolynomial (Fin 3) K
abbrev Series := PowerSeries Base

private instance : CharZero Series := PowerSeries.constantCoeff.charZero

/-- Solving the two labels for the first two coordinate squares. -/
def radicand₀ : Base :=
  MvPolynomial.C (9/16 : K)*MvPolynomial.X 0^2-
  MvPolynomial.C (15/16 : K)*MvPolynomial.X 1^2-
  MvPolynomial.C (14/16 : K)*MvPolynomial.X 2^2

def radicand₁ : Base :=
  -MvPolynomial.C (25/16 : K)*MvPolynomial.X 0^2-
  MvPolynomial.C (1/16 : K)*MvPolynomial.X 1^2-
  MvPolynomial.C (2/16 : K)*MvPolynomial.X 2^2

abbrev FirstRoot := QuadraticAlgebra Base radicand₁ 0
abbrev ConeRing := QuadraticAlgebra FirstRoot (algebraMap Base FirstRoot radicand₀) 0

private def point : Fin 3 → K := ![80,52,16]

private def polynomialShift : Base →+* Polynomial Base :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j ↦ Polynomial.C (MvPolynomial.C (point j))+
      Polynomial.X*Polynomial.C (MvPolynomial.X j))

private def shiftBack : Polynomial Base →+* Base :=
  (MvPolynomial.eval₂Hom MvPolynomial.C (fun j ↦ MvPolynomial.X j-MvPolynomial.C (point j))).comp
    (Polynomial.evalRingHom 1)

private lemma shiftBack_shift (P : Base) : shiftBack (polynomialShift P) = P := by
  have he : shiftBack.comp polynomialShift = RingHom.id Base := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shiftBack,polynomialShift]
    · intro j
      simp [shiftBack,polynomialShift]
  exact congrArg (fun f : Base →+* Base ↦ f P) he

private def formalShift : Base →+* Series :=
  Polynomial.coeToPowerSeries.ringHom.comp polynomialShift

private lemma formalShift_injective : Function.Injective formalShift := by
  intro P Q h
  have hp : polynomialShift P = polynomialShift Q := Polynomial.coe_injective Base h
  have hh := congrArg shiftBack hp
  simpa only [shiftBack_shift] using hh

private lemma formalShift_constantCoeff (P : Base) :
    PowerSeries.constantCoeff (formalShift P) = MvPolynomial.C (MvPolynomial.eval point P) := by
  have he : PowerSeries.constantCoeff.comp formalShift =
      MvPolynomial.C.comp (MvPolynomial.eval point) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [formalShift,polynomialShift]
    · intro j
      simp [formalShift,polynomialShift]
  exact congrArg (fun f : Base →+* Base ↦ f P) he

private lemma formal_sqrt (P : Base) (r : K) (hr : r ≠ 0)
    (hP : MvPolynomial.eval point P = r^2) :
    ∃ y : Series, y^2 = formalShift P ∧ y ≠ 0 := by
  let c : Series := PowerSeries.C (MvPolynomial.C (r^2))
  let ci : Series := PowerSeries.C (MvPolynomial.C ((r^2)⁻¹))
  have hci : c*ci = 1 := by
    simp only [c,ci,←map_mul,mul_inv_cancel₀ (pow_ne_zero _ hr),map_one]
  let u : Series := ci*formalShift P-1
  have hu : PowerSeries.constantCoeff u = 0 := by
    simp only [u,ci,map_sub,map_mul,map_one,PowerSeries.constantCoeff_C,
      formalShift_constantCoeff,hP]
    rw [←map_mul,inv_mul_cancel₀ (pow_ne_zero _ hr),map_one,sub_self]
  obtain ⟨b,hb⟩ := fourth_root_one_add u hu
  let y : Series := PowerSeries.C (MvPolynomial.C r)*b^2
  have hy : y^2 = formalShift P := by
    have he : y^2 = c*b^4 := by
      dsimp [y,c]
      simp only [map_pow]
      ring
    rw [he,hb]
    dsimp only [u]
    linear_combination hci*formalShift P
  refine ⟨y,hy,?_⟩
  intro hz
  have hh := congrArg PowerSeries.constantCoeff hy
  rw [hz] at hh
  simp only [zero_pow (by decide : 2 ≠ 0),map_zero,formalShift_constantCoeff,hP] at hh
  exact hr (by simpa using hh.symm)

private lemma roots_exist :
    (∃ y : Series, y^2 = formalShift radicand₀ ∧ y ≠ 0) ∧
    (∃ y : Series, y^2 = formalShift radicand₁ ∧ y ≠ 0) := by
  constructor
  · apply formal_sqrt radicand₀ (29 : K) (by norm_num)
    norm_num [radicand₀,point,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · apply formal_sqrt radicand₁ (101*imag) (mul_ne_zero (by norm_num) imag_ne_zero)
    norm_num [radicand₁,point,mul_pow,imag_sq,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

/-- All-degree anisotropy in the algebra with the two quadratic relations.
The statement applies to arbitrary elements of that algebra, not merely to
linear or quadratic polynomials. -/
theorem cone_ring_anisotropic : FourthAnisotropic ConeRing := by
  obtain ⟨⟨r,hr,hr0⟩,⟨s,hs,hs0⟩⟩ := roots_exist
  exact double_quadratic_anisotropic radicand₀ radicand₁ formalShift formalShift_injective
    r s hr hs hr0 hs0 (powerSeries_anisotropic (mvPolynomial_anisotropic gaussian_anisotropic))

end
end Erdos322Research.JointQuadraticCone
