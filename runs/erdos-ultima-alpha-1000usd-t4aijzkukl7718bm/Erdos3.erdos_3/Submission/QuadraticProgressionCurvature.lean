import Submission.LocalQuadraticProgressions

/-! Exact curvature on arbitrary subprogressions. Three nearly equal phase
values control the square-dilate of the common quadratic coefficient. -/
namespace Erdos3QuadraticProgressionCurvature
open Erdos3LocalQuadraticProgressions Erdos3FiniteUniformity Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

lemma two_choose_two_add (n : ℕ) : 2*(n.choose 2)+n = n^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    nlinarith

lemma choose_two_second_difference (m d : ℕ) :
    (m+2*d).choose 2+m.choose 2 = 2*((m+d).choose 2)+d^2 := by
  have h0 := two_choose_two_add m
  have h1 := two_choose_two_add (m+d)
  have h2 := two_choose_two_add (m+2*d)
  nlinarith

lemma binomial_phase_three_point (A u v : ℂ) (m d : ℕ) :
    (A*u^(m+2*d)*v^((m+2*d).choose 2))*(A*u^m*v^(m.choose 2)) =
      (A*u^(m+d)*v^((m+d).choose 2))^2*v^(d^2) := by
  calc
    _ = A^2*u^(m+2*d+m)*v^((m+2*d).choose 2+m.choose 2) := by rw [pow_add,pow_add]; ring
    _ = A^2*u^(2*(m+d))*v^(2*((m+d).choose 2)+d^2) := by
      rw [choose_two_second_difference,show m+2*d+m = 2*(m+d) by omega]
    _ = _ := by rw [pow_add,pow_mul,pow_mul]; ring

lemma three_point_curvature_bound {A B C v : ℂ}
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (he : C*A = B^2*v) : ‖v-1‖ ≤ ‖C-B‖+‖A-B‖ := by
  have hb2 : ‖B^2‖ = 1 := by rw [norm_pow,hB,one_pow]
  calc
    _ = ‖B^2*(v-1)‖ := by rw [norm_mul,hb2,one_mul]
    _ = ‖C*A-B^2‖ := by rw [mul_sub,mul_one,← he]
    _ = ‖(C-B)*A+B*(A-B)‖ := by congr 1; ring
    _ ≤ ‖(C-B)*A‖+‖B*(A-B)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul,hA,hB,mul_one,one_mul]

variable {G : Type*} [AddCommGroup G]

lemma progression_shift (a h : G) (m d : ℕ) : (a+m • h)+d • h = a+(m+d) • h := by
  simp only [add_nsmul,add_assoc]

/-- The second derivative at stride d is the d²-th power of the original
curvature, regardless of the new base point. All needed points stay local. -/
theorem local_curvature_subprogression {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (a h : G) {N : ℕ} (hR : ∀ n ≤ N, a+n • h ∈ R) {m d : ℕ} (hmd : m+2*d ≤ N) :
    derivative (derivative q (d • h)) (d • h) (a+m • h) =
      (derivative (derivative q h) h a)^(d^2) := by
  have hprod : q (a+(m+2*d) • h)*q (a+m • h) =
      (q (a+(m+d) • h))^2*(derivative (derivative q h) h a)^(d^2) := by
    rw [local_quadratic_progression_formula hq hquad a h hR (m+2*d) hmd,
      local_quadratic_progression_formula hq hquad a h hR m (by omega),
      local_quadratic_progression_formula hq hquad a h hR (m+d) (by omega)]
    exact binomial_phase_three_point _ _ _ m d
  have hunit := mul_conj_eq_one (hq (a+(m+d) • h))
  calc
    _ = (q (a+(m+2*d) • h)*q (a+m • h))*(conj (q (a+(m+d) • h)))^2 := by
      simp only [derivative,map_mul,starRingEnd_self_apply,progression_shift]
      rw [show m+d+d = m+2*d by omega]
      ring
    _ = (q (a+(m+d) • h))^2*(derivative (derivative q h) h a)^(d^2)*
        (conj (q (a+(m+d) • h)))^2 := by rw [hprod]
    _ = (derivative (derivative q h) h a)^(d^2)*
        (q (a+(m+d) • h)*conj (q (a+(m+d) • h)))^2 := by ring
    _ = _ := by rw [hunit,one_pow,mul_one]

/-- Three nearly equal phase values produce small curvature at the new stride. -/
theorem local_curvature_bound_from_three_points {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (a h : G) {N : ℕ} (hR : ∀ n ≤ N, a+n • h ∈ R) {m d : ℕ} (hmd : m+2*d ≤ N) :
    ‖(derivative (derivative q h) h a)^(d^2)-1‖ ≤
      ‖q (a+(m+2*d) • h)-q (a+(m+d) • h)‖+‖q (a+m • h)-q (a+(m+d) • h)‖ := by
  apply three_point_curvature_bound (hq _) (hq _) (hq _)
  rw [local_quadratic_progression_formula hq hquad a h hR (m+2*d) hmd,
    local_quadratic_progression_formula hq hquad a h hR m (by omega),
    local_quadratic_progression_formula hq hquad a h hR (m+d) (by omega)]
  exact binomial_phase_three_point _ _ _ m d

#print axioms local_curvature_subprogression
#print axioms local_curvature_bound_from_three_points
end Erdos3QuadraticProgressionCurvature
