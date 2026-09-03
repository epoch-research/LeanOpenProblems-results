import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

/-! Exact square classification for the generic elliptic duplication map.
This classifies a symbolic square condition; it does not classify square
values at rational points and does not settle the integral-distance problem. -/
namespace Erdos213.EllipticDuplication
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000

/-- Short Weierstrass cubic. -/
def cubic (A B : ℚ) : ℚ[X] := X^3+C A*X+C B

/-- Numerator of x(2P)-k, with denominator 4*y(P)^2. -/
def quartic (A B k : ℚ) : ℚ[X] :=
  X^4+C (-4*k)*X^3+C (-2*A)*X^2+C (-8*B-4*A*k)*X+C (A^2-4*B*k)

def candidate (A k : ℚ) : ℚ[X] := X^2+C (-2*k)*X-C (A+2*k^2)

lemma quartic_identity (A B k : ℚ) :
    quartic A B k = (candidate A k)^2-C (4*(k^3+A*k+B))*(2*X+C k) := by
  apply Polynomial.funext
  intro t
  simp [quartic,candidate]
  ring

/-- Exact bridge from the standard tangent-slope duplication formula to
its shifted numerator. -/
lemma duplication_numerator (A B k : ℚ) :
    quartic A B k=(3*X^2+C A)^2-4*cubic A B*(2*X+C k) := by
  apply Polynomial.funext
  intro t
  simp [quartic,cubic]
  ring

lemma quartic_degree (A B k : ℚ) : (quartic A B k).natDegree = 4 := by
  unfold quartic
  compute_degree!

lemma cubic_degree (A B : ℚ) : (cubic A B).natDegree = 3 := by
  unfold cubic
  compute_degree!

lemma quartic_ne_zero (A B k : ℚ) : quartic A B k ≠ 0 := by
  intro h
  have hd := quartic_degree A B k
  rw [h,natDegree_zero] at hd
  contradiction

lemma cubic_ne_zero (A B : ℚ) : cubic A B ≠ 0 := by
  intro h
  have hd := cubic_degree A B
  rw [h,natDegree_zero] at hd
  contradiction

/-- The quartic is a polynomial square exactly at a two-torsion x-value.
The proof needs only its coefficients of degrees one through four. -/
theorem quartic_square_iff (A B k : ℚ) :
    IsSquare (quartic A B k) ↔ k^3+A*k+B=0 := by
  constructor
  · rintro ⟨p,hp⟩
    have hp0 : p ≠ 0 := by
      intro he
      exact quartic_ne_zero A B k (by simpa [he] using hp)
    have hd := congrArg natDegree hp
    rw [quartic_degree,natDegree_mul hp0 hp0] at hd
    have hdeg : p.natDegree < 3 := by omega
    have hrep := p.as_sum_range_C_mul_X_pow' hdeg
    have hpsq : p*p = C ((p.coeff 0)^2)+C (2*p.coeff 0*p.coeff 1)*X+
        C ((p.coeff 1)^2+2*p.coeff 0*p.coeff 2)*X^2+
        C (2*p.coeff 1*p.coeff 2)*X^3+C ((p.coeff 2)^2)*X^4 := by
      apply Polynomial.funext
      intro t
      conv_lhs => rw [hrep]
      simp [Finset.sum_range_succ]
      ring
    rw [hpsq] at hp
    have h1 := congrArg (fun p : ℚ[X] => p.coeff 1) hp
    have h2 := congrArg (fun p : ℚ[X] => p.coeff 2) hp
    have h3 := congrArg (fun p : ℚ[X] => p.coeff 3) hp
    have h4 := congrArg (fun p : ℚ[X] => p.coeff 4) hp
    simp only [quartic,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,coeff_X_pow] at h1 h2 h3 h4
    norm_num at h1 h2 h3 h4
    have hp1 : p.coeff 1 = -2*k*p.coeff 2 := by
      linear_combination -(p.coeff 2)*h3/2 + (p.coeff 1)*h4
    have hp0' : p.coeff 0*p.coeff 2 = -A-2*k^2 := by
      rw [hp1] at h2
      linear_combination -h2/2+2*k^2*h4
    rw [hp1] at h1
    linear_combination -h1/8+k*hp0'/2
  · intro hk
    refine ⟨candidate A k,?_⟩
    rw [quartic_identity,hk]
    simp [pow_two]

lemma polynomial_square_of_ratFunc_square (p : ℚ[X])
    (h : IsSquare (algebraMap ℚ[X] (RatFunc ℚ) p)) : IsSquare p := by
  obtain ⟨r,hr⟩ := h
  have hint : IsIntegral ℚ[X] (r^2) := by
    rw [pow_two, ← hr]
    exact isIntegral_algebraMap
  obtain ⟨q,hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := ℚ[X]) (K := RatFunc ℚ) (by norm_num : 0 < (2 : ℕ)) hint
  refine ⟨q,?_⟩
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simpa [map_mul,hq] using hr

lemma ratFunc_quartic_square_iff (A B k : ℚ) :
    IsSquare (algebraMap ℚ[X] (RatFunc ℚ) (quartic A B k)) ↔ k^3+A*k+B=0 := by
  constructor
  · intro h
    exact (quartic_square_iff A B k).mp (polynomial_square_of_ratFunc_square _ h)
  · intro h
    exact ((quartic_square_iff A B k).mpr h).map (algebraMap ℚ[X] (RatFunc ℚ))

abbrev F := RatFunc ℚ
abbrev lift (p : ℚ[X]) : F := algebraMap ℚ[X] F p

lemma lift_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : lift p ≠ 0 := by
  simpa only [lift,map_zero] using (IsFractionRing.injective ℚ[X] F).ne hp

/-- The rational-function part alone cannot be a square: after multiplying
by a square, the numerator has odd degree seven. -/
lemma rational_part_not_square (A B k : ℚ) :
    ¬ IsSquare (lift (quartic A B k)/(4*lift (cubic A B))) := by
  intro h
  have hf : lift (cubic A B) ≠ 0 := lift_ne_zero (cubic_ne_zero A B)
  have he : lift (quartic A B k*cubic A B) =
      (2*lift (cubic A B))^2*(lift (quartic A B k)/(4*lift (cubic A B))) := by
    simp only [lift,map_mul]
    field_simp
    ring
  have hprod : IsSquare (lift (quartic A B k*cubic A B)) := by
    rw [he]
    exact (IsSquare.sq _).mul h
  obtain ⟨p,hp⟩ := polynomial_square_of_ratFunc_square _ hprod
  have hp0 : p ≠ 0 := by
    intro hz
    have hz' : quartic A B k*cubic A B = 0 := by simpa [hz] using hp
    exact mul_ne_zero (quartic_ne_zero A B k) (cubic_ne_zero A B) hz'
  have hd := congrArg natDegree hp
  rw [natDegree_mul (quartic_ne_zero A B k) (cubic_ne_zero A B),
    quartic_degree,cubic_degree,natDegree_mul hp0 hp0] at hd
  omega

lemma cubic_lift_not_square (A B : ℚ) : ¬ IsSquare (lift (cubic A B)) := by
  intro h
  obtain ⟨p,hp⟩ := polynomial_square_of_ratFunc_square _ h
  have hp0 : p ≠ 0 := by
    intro hz
    exact cubic_ne_zero A B (by simpa [hz] using hp)
  have hd := congrArg natDegree hp
  rw [cubic_degree,natDegree_mul hp0 hp0] at hd
  omega

instance elliptic_field_condition (A B : ℚ) :
    Fact (∀ r : F, r^2 ≠ lift (cubic A B)+0*r) := ⟨by
  intro r hr
  apply cubic_lift_not_square A B
  refine ⟨r,?_⟩
  simpa only [zero_mul,add_zero,pow_two] using hr.symm⟩

/-- The generic elliptic coordinate algebra, with y^2 = x^3+A*x+B. -/
abbrev E (A B : ℚ) := QuadraticAlgebra F (lift (cubic A B)) 0

/-- In the generic elliptic function field, x(2P)-k is a square if and only
if k is a root of the cubic. This is a symbolic statement, not a bound on
individual rational specializations or on sequences of rational points. -/
theorem elliptic_square_iff (A B k : ℚ) :
    IsSquare (algebraMap F (E A B) (lift (quartic A B k)/(4*lift (cubic A B)))) ↔
      k^3+A*k+B=0 := by
  have hf : lift (cubic A B) ≠ 0 := lift_ne_zero (cubic_ne_zero A B)
  constructor
  · rintro ⟨z,hz⟩
    have hre := congrArg QuadraticAlgebra.re hz
    have him := congrArg QuadraticAlgebra.im hz
    simp only [QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.re_mul] at hre
    simp only [QuadraticAlgebra.algebraMap_im,QuadraticAlgebra.im_mul,
      zero_mul,add_zero] at him
    have hrs : z.re*z.im=0 := by linear_combination -him/2
    rcases mul_eq_zero.mp hrs with hr | hi
    · have hq : IsSquare (lift (quartic A B k)) := by
        refine ⟨2*lift (cubic A B)*z.im,?_⟩
        rw [hr] at hre
        simp only [zero_mul,zero_add] at hre
        field_simp at hre
        calc
          _ = 4*lift (cubic A B)^2*z.im^2 := hre
          _ = _ := by ring
      exact (ratFunc_quartic_square_iff A B k).mp hq
    · apply (rational_part_not_square A B k).elim
      refine ⟨z.re,?_⟩
      simpa only [hi,mul_zero,add_zero] using hre
  · intro hk
    obtain ⟨q,hq⟩ := (ratFunc_quartic_square_iff A B k).mpr hk
    change lift (quartic A B k) = q*q at hq
    refine ⟨⟨0,q/(2*lift (cubic A B))⟩,?_⟩
    ext
    · simp only [QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.re_mul,
        zero_mul,zero_add]
      rw [hq]
      field_simp
      ring
    · simp only [QuadraticAlgebra.algebraMap_im,QuadraticAlgebra.im_mul,
        zero_mul,mul_zero,add_zero]

#print axioms duplication_numerator
#print axioms quartic_square_iff
#print axioms ratFunc_quartic_square_iff
#print axioms rational_part_not_square
#print axioms elliptic_square_iff
end
end Erdos213.EllipticDuplication
