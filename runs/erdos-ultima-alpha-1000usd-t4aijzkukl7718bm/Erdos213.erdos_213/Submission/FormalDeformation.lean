import Submission.OrthogonalGlobal
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Formal square roots do not provide rational-distance specializations.
The formal lifting theorem applies to arbitrary deformations of distinct
collinear rational points. The explicit parabola family has these lifts but,
from four points onward, no nonzero rational parameter gives rational distances.
This is not a bound on arbitrary configurations or a settlement of Erdős 213. -/
namespace Erdos213.FormalDeformation
open PowerSeries
noncomputable section
set_option maxHeartbeats 2000000

lemma half_series_square :
    (binomialSeries ℚ (1/2 : ℚ))^2 = (1 + X : PowerSeries ℚ) := by
  rw [pow_two, ← binomialSeries_add]
  norm_num only [show (1/2 : ℚ)+1/2=1 by norm_num]
  simpa using binomialSeries_nat (R := ℚ) (A := ℚ) 1

/-- Every rational series with constant term one has a rational series square root. -/
theorem isSquare_of_constantCoeff_one (f : PowerSeries ℚ)
    (hf : constantCoeff f = 1) : IsSquare f := by
  have hg : HasSubst (f-1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  have he := congrArg (substAlgHom (R := ℚ) hg) half_series_square
  have hs : (substAlgHom (R := ℚ) hg (binomialSeries ℚ (1/2 : ℚ)))^2 = f := by
    simpa [substAlgHom_X] using he
  exact ⟨_, by simpa only [pow_two] using hs.symm⟩

/-- A nonzero square constant term is sufficient, with no degree or jet cutoff. -/
theorem isSquare_of_constantCoeff_square {f : PowerSeries ℚ} {a : ℚ}
    (ha : a ≠ 0) (hf : constantCoeff f = a^2) : IsSquare f := by
  have hg : constantCoeff (C (a⁻¹)^2*f) = 1 := by simp [hf, ha]
  obtain ⟨g,hg⟩ := isSquare_of_constantCoeff_one (C (a⁻¹)^2*f) hg
  refine ⟨C a*g, ?_⟩
  have hca : C a*C a⁻¹ = (1 : PowerSeries ℚ) := by rw [← map_mul]; simp [ha]
  calc
    f = (C a*C a⁻¹)^2*f := by rw [hca]; ring
    _ = C a^2*(C a⁻¹^2*f) := by ring
    _ = C a^2*(g*g) := by rw [hg]
    _ = (C a*g)*(C a*g) := by ring

/-- All formal coordinate deformations of distinct points on the x-axis lift
simultaneously to formal distance square roots. The roots are series, not
rational functions and not rational numbers at nonzero rational parameters. -/
theorem collinear_deformation_squares {ι : Type*} (x y : ι → PowerSeries ℚ)
    (a : ι → ℚ) (ha : Function.Injective a)
    (hx : ∀ i, constantCoeff (x i) = a i) (hy : ∀ i, constantCoeff (y i) = 0) :
    ∀ i j, IsSquare ((x i-x j)^2+(y i-y j)^2) := by
  intro i j
  by_cases hij : i=j
  · subst j; simp
  · apply isSquare_of_constantCoeff_square (sub_ne_zero.mpr (ha.ne hij))
    simp [hx,hy]

section Algebra
variable {R : Type*} [CommRing R]

def sqDistance (t a b : R) : R := (a-b)^2+(t*a^2-t*b^2)^2

def triangle (t a b c : R) : R :=
  (b-a)*(t*c^2-t*a^2)-(t*b^2-t*a^2)*(c-a)

def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def circle (t a b c d : R) : R :=
  det3 (b-a) (t*b^2-t*a^2) (sqDistance t b a)
    (c-a) (t*c^2-t*a^2) (sqDistance t c a)
    (d-a) (t*d^2-t*a^2) (sqDistance t d a)

lemma sqDistance_factorization (t a b : R) :
    sqDistance t a b=(a-b)^2*(1+(t*(a+b))^2) := by unfold sqDistance; ring

lemma triangle_factorization (t a b c : R) :
    triangle t a b c=t*(b-a)*(c-a)*(c-b) := by unfold triangle; ring

lemma circle_factorization (t a b c d : R) :
    circle t a b c d=
      t^3*(b-a)*(c-a)*(d-a)*(c-b)*(d-b)*(d-c)*(a+b+c+d) := by
  unfold circle det3 sqDistance
  ring
end Algebra

/-- Explicit arbitrary-size formal configurations, using positive integer
parameters 1,...,n. The distance identity also holds for all rational a,b. -/
theorem parabola_formal_squares (a b : ℚ) :
    IsSquare (sqDistance (X : PowerSeries ℚ) (C a) (C b)) := by
  rw [sqDistance_factorization]
  apply (IsSquare.sq _).mul
  apply isSquare_of_constantCoeff_one
  simp

lemma C_ne_zero {a : ℚ} (ha : a ≠ 0) : (C a : PowerSeries ℚ) ≠ 0 := by
  intro h
  exact ha (by simpa using congrArg constantCoeff h)

lemma formal_triangle_ne_zero {a b c : ℚ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triangle (X : PowerSeries ℚ) (C a) (C b) (C c) ≠ 0 := by
  rw [triangle_factorization]
  have hba : (C b-C a : PowerSeries ℚ) ≠ 0 := by
    rw [← map_sub]; exact C_ne_zero (sub_ne_zero.mpr hab.symm)
  have hca : (C c-C a : PowerSeries ℚ) ≠ 0 := by
    rw [← map_sub]; exact C_ne_zero (sub_ne_zero.mpr hac.symm)
  have hcb : (C c-C b : PowerSeries ℚ) ≠ 0 := by
    rw [← map_sub]; exact C_ne_zero (sub_ne_zero.mpr hbc.symm)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero X_ne_zero hba) hca) hcb

lemma formal_circle_ne_zero {a b c d : ℚ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hs : a+b+c+d ≠ 0) :
    circle (X : PowerSeries ℚ) (C a) (C b) (C c) (C d) ≠ 0 := by
  rw [circle_factorization]
  simp only [← map_sub, ← map_add]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero)
      (C_ne_zero (sub_ne_zero.mpr hab.symm))) (C_ne_zero (sub_ne_zero.mpr hac.symm)))
      (C_ne_zero (sub_ne_zero.mpr had.symm))) (C_ne_zero (sub_ne_zero.mpr hbc.symm)))
      (C_ne_zero (sub_ne_zero.mpr hbd.symm))) (C_ne_zero (sub_ne_zero.mpr hcd.symm)))
      (C_ne_zero hs)

/-- The two lengths corresponding to parameter pairs (1,2) and (2,4) already
obstruct every nonzero rational specialization, by the completed global descent. -/
theorem two_edges_force_zero {t : ℚ}
    (h12 : IsSquare (sqDistance t 1 2)) (h24 : IsSquare (sqDistance t 2 4)) : t=0 := by
  by_contra ht
  apply OrthogonalGlobal.no_simultaneous_squares (u := (3*t)⁻¹) (inv_ne_zero (by aesop))
  constructor
  · convert h12.div (IsSquare.sq (3*t)) using 1
    dsimp [sqDistance]
    field_simp
    ring
  · convert h24.div (IsSquare.sq (6*t)) using 1
    dsimp [sqDistance]
    field_simp
    ring

/-- Truncating a formal square root solves every prescribed finite jet over Q.
This statement does not say the truncated polynomial is an exact square root. -/
theorem square_jets {f : PowerSeries ℚ} (hf : IsSquare f) (N : ℕ) :
    ∃ p : Polynomial ℚ, p.degree < N ∧
      ∀ k < N, coeff k ((p : PowerSeries ℚ)^2) = coeff k f := by
  obtain ⟨g,rfl⟩ := hf
  refine ⟨trunc N g, degree_trunc_lt g N, ?_⟩
  intro k hk
  rw [pow_two, ← coeff_mul_eq_coeff_trunc_mul_trunc g g hk]

/-- Positive integer parameters, for an arbitrary requested cardinality. -/
def parameter {n : ℕ} (i : Fin n) : ℚ := (i.val : ℚ)+1

lemma parameter_injective (n : ℕ) : Function.Injective (parameter (n := n)) := by
  intro i j hij
  apply Fin.ext
  have h : (i.val : ℚ) = j.val := by simpa [parameter] using hij
  exact_mod_cast h

lemma parameter_pos {n : ℕ} (i : Fin n) : 0 < parameter i := by
  dsimp [parameter]
  positivity

/-- Arbitrarily large formal general-position configurations, stated using
nonzero coordinate determinants in Q[[X]]. This is not a real integral-distance
configuration. All roots exist formally, while every rational specialization
with rational distances is collapsed when n >= 4. -/
theorem arbitrary_formal_configurations (n : ℕ) :
    Function.Injective (fun i : Fin n => (C (parameter i) : PowerSeries ℚ)) ∧
    (∀ i j : Fin n, IsSquare (sqDistance X (C (parameter i)) (C (parameter j)))) ∧
    (∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
      triangle X (C (parameter i)) (C (parameter j)) (C (parameter k)) ≠ 0) ∧
    (∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      circle X (C (parameter i)) (C (parameter j)) (C (parameter k))
        (C (parameter l)) ≠ 0) := by
  refine ⟨?_,fun i j => parabola_formal_squares _ _,?_,?_⟩
  · intro i j hij
    apply parameter_injective n
    simpa using congrArg constantCoeff hij
  · intro i j k hij hik hjk
    exact formal_triangle_ne_zero ((parameter_injective n).ne hij)
      ((parameter_injective n).ne hik) ((parameter_injective n).ne hjk)
  · intro i j k l hij hik hil hjk hjl hkl
    apply formal_circle_ne_zero ((parameter_injective n).ne hij)
      ((parameter_injective n).ne hik) ((parameter_injective n).ne hil)
      ((parameter_injective n).ne hjk) ((parameter_injective n).ne hjl)
      ((parameter_injective n).ne hkl)
    exact ne_of_gt (add_pos (add_pos (add_pos (parameter_pos i)
      (parameter_pos j)) (parameter_pos k)) (parameter_pos l))

theorem rational_specialization_iff {n : ℕ} (hn : 4 ≤ n) (t : ℚ) :
    (∀ i j : Fin n, IsSquare (sqDistance t (parameter i) (parameter j))) ↔ t=0 := by
  constructor
  · intro h
    apply two_edges_force_zero
    · convert h ⟨0,by omega⟩ ⟨1,by omega⟩ using 1
      norm_num [parameter]
    · convert h ⟨1,by omega⟩ ⟨3,by omega⟩ using 1
      norm_num [parameter]
  · rintro rfl
    intro i j
    simpa [sqDistance] using IsSquare.sq (parameter i-parameter j)

#print axioms isSquare_of_constantCoeff_one
#print axioms collinear_deformation_squares
#print axioms parabola_formal_squares
#print axioms formal_triangle_ne_zero
#print axioms formal_circle_ne_zero
#print axioms two_edges_force_zero
#print axioms square_jets
#print axioms arbitrary_formal_configurations
#print axioms rational_specialization_iff
end
end Erdos213.FormalDeformation
