import Submission.SimultaneousQuadraticRecurrence

/-! Uniform flattening of finitely many local quadratic phases along a shorter
arithmetic progression through a specified base point. -/
namespace Erdos3LocalQuadraticFlattening
open Erdos3LocalQuadraticProgressions Erdos3QuadraticProgressionCurvature
  Erdos3SimultaneousQuadraticRecurrence Erdos3FiniteUniformity Erdos3LocalQuadraticInverse
  Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

/-- Exact square-root choice converts binomial coordinates into monomial
coordinates. No claim about the root being close to one is made. -/
lemma exists_monomial_phase_representation {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ w z : ℂ, ‖w‖ = 1 ∧ ‖z‖ = 1 ∧ ∀ n : ℕ, u^n*v^(n.choose 2) = w^n*z^(n^2) := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq v (by decide : 0 < 2)
  have hzn : ‖z‖ = 1 := by
    have hh := congrArg norm hz
    rw [norm_pow,hv] at hh
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzn]; norm_num)
  refine ⟨u/z,z,by rw [norm_div,hu,hzn,div_one],hzn,?_⟩
  intro n
  rw [← two_choose_two_add n,pow_add,pow_mul,hz,div_pow]
  field_simp

variable {G : Type*} [AddCommGroup G] {I : Type*} [Fintype I]

/-- If the initial progression stays in the common local domain, a uniformly
bounded positive stride flattens every phase on a prescribed shorter progression.
This is an oscillation statement, not a density-preserving partition theorem. -/
theorem simultaneous_local_quadratic_flattening
    (R : Set G) (q : I → G → ℂ) (hq : ∀ i x, ‖q i x‖ = 1)
    (hquad : ∀ i, IsLocallyQuadratic R (q i)) (a h : G) (L t : ℕ) (hL : 0 < L)
    (hR : ∀ n ≤ L*recurrenceBound (2*Fintype.card I) t, a+n • h ∈ R) :
    ∃ d : ℕ, 0 < d ∧ d < recurrenceBound (2*Fintype.card I) t ∧
      ∀ i, ∀ n ≤ L, ‖q i (a+(n*d) • h)-q i a‖ ≤ 2*(L : ℝ)^2*(1/2 : ℝ)^t := by
  have hrep (i : I) : ∃ w z : ℂ, ‖w‖ = 1 ∧ ‖z‖ = 1 ∧ ∀ n : ℕ,
      (derivative (q i) h a)^n*(derivative (derivative (q i) h) h a)^(n.choose 2) = w^n*z^(n^2) :=
    exists_monomial_phase_representation (derivative_norm_one (q i) (hq i) h a)
      (derivative_norm_one (derivative (q i) h) (derivative_norm_one (q i) (hq i) h) h a)
  choose w z hw hz hrep using hrep
  obtain ⟨d,hd,hbound,hwd,hzd⟩ := simultaneous_mixed_recurrence w z hw hz t
  have hbound' : d < recurrenceBound (2*Fintype.card I) t := by
    simpa only [two_mul] using hbound
  refine ⟨d,hd,hbound',?_⟩
  intro i n hn
  have hindex : n*d ≤ L*recurrenceBound (2*Fintype.card I) t := Nat.mul_le_mul hn hbound'.le
  have hformula : q i (a+(n*d) • h) = q i a*(w i)^ (n*d)*(z i)^((n*d)^2) := by
    rw [local_quadratic_progression_formula (hq i) (hquad i) a h hR (n*d) hindex,mul_assoc,hrep]
    ring
  have hreindex : (w i)^(n*d)*(z i)^((n*d)^2) = ((w i)^d)^n*((z i)^(d^2))^(n^2) := by
    rw [← pow_mul,← pow_mul]
    congr 1 <;> ring
  have he : q i (a+(n*d) • h)-q i a = q i a*(((w i)^d)^n*((z i)^(d^2))^(n^2)-1) := by
    rw [hformula]
    rw [mul_assoc,hreindex]
    ring
  rw [he,norm_mul,hq,one_mul]
  have hwn : ‖(w i)^d‖ = 1 := by rw [norm_pow,hw,one_pow]
  have hzn : ‖(z i)^(d^2)‖ = 1 := by rw [norm_pow,hz,one_pow]
  have hosc := (norm_mul_sub_one_le (by rw [norm_pow,hwn,one_pow] : ‖((w i)^d)^n‖ = 1)
    (w := ((z i)^(d^2))^(n^2))).trans
      (add_le_add (unit_power_oscillation _ hwn n) (unit_power_oscillation _ hzn (n^2)))
  have hcoeff : (n : ℝ)+(n : ℝ)^2 ≤ 2*(L : ℝ)^2 := by
    have hnR : (n : ℝ) ≤ L := by exact_mod_cast hn
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith only [hnR,hLR,hn0]
  calc
    _ ≤ (n : ℝ)*‖(w i)^d-1‖+(n^2 : ℕ)*‖(z i)^(d^2)-1‖ := hosc
    _ ≤ (n : ℝ)*(1/2 : ℝ)^t+(n^2 : ℕ)*(1/2 : ℝ)^t :=
      add_le_add (mul_le_mul_of_nonneg_left (hwd i) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (hzd i) (Nat.cast_nonneg _))
    _ = ((n : ℝ)+(n : ℝ)^2)*(1/2 : ℝ)^t := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)

#print axioms simultaneous_local_quadratic_flattening
end Erdos3LocalQuadraticFlattening
