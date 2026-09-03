import Submission.LocalQuadraticInverse

/-! Exact binomial-polynomial formulas and oscillation bounds for a locally
quadratic unit phase along arithmetic progressions in its domain. -/
namespace Erdos3LocalQuadraticProgressions
open Erdos3FiniteUniformity Erdos3LocalQuadraticInverse Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

lemma derivative_norm_one {G : Type*} [AddCommGroup G] (q : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (h x : G) : ‖derivative q h x‖ = 1 := by
  simp only [derivative,norm_mul,Complex.norm_conj,hq,one_mul]

lemma unit_conj_cancel {a b c : ℂ} (hb : ‖b‖ = 1) (h : a*conj b = c) : a = c*b := by
  have hu : conj b*b = 1 := by simpa only [mul_comm] using mul_conj_eq_one hb
  calc
    a = a*(conj b*b) := by rw [hu,mul_one]
    _ = (a*conj b)*b := by ring
    _ = c*b := by rw [h]

lemma binomial_sequence_formula (a : ℕ → ℂ) (u v : ℂ) {N : ℕ}
    (hstep : ∀ n < N, a (n+1) = a n*(u*v^n)) :
    ∀ n ≤ N, a n = a 0*u^n*v^(n.choose 2) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hstep n (by omega),ih (by omega)]
    rw [Nat.choose_succ_succ,Nat.choose_one_right,pow_add,pow_succ]
    ring

variable {G : Type*} [AddCommGroup G]

lemma progression_step (a d : G) (n : ℕ) : (a+n • d)+d = a+(n+1) • d := by
  simp only [add_nsmul,one_nsmul,add_assoc]

lemma local_second_derivative_constant {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (a d : G) {N : ℕ} (hR : ∀ n ≤ N, a+n • d ∈ R) :
    ∀ n, n+2 ≤ N → derivative (derivative q d) d (a+n • d) = derivative (derivative q d) d a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have he := hquad (a+n • d) d d d (hR n (by omega))
      (by simpa only [progression_step] using hR (n+1) (by omega))
      (by simpa only [progression_step] using hR (n+1) (by omega))
      (by simpa only [progression_step] using hR (n+1+1) (by omega))
      (by simpa only [progression_step] using hR (n+1) (by omega))
      (by simpa only [progression_step] using hR (n+1+1) (by omega))
      (by simpa only [progression_step] using hR (n+1+1) (by omega))
      (by simpa only [progression_step] using hR (n+1+1+1) (by omega))
    change derivative (derivative q d) d ((a+n • d)+d)*
      conj (derivative (derivative q d) d (a+n • d)) = 1 at he
    have hb := derivative_norm_one (derivative q d) (derivative_norm_one q hq d) d (a+n • d)
    have hh := unit_conj_cancel hb he
    rw [one_mul,progression_step] at hh
    exact hh.trans (ih (by omega))

lemma local_first_derivative_formula {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (a d : G) {N : ℕ} (hR : ∀ n ≤ N, a+n • d ∈ R) :
    ∀ n, n+1 ≤ N → derivative q d (a+n • d) =
      derivative q d a*(derivative (derivative q d) d a)^n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have he := local_second_derivative_constant hq hquad a d hR n (by omega)
    change derivative q d ((a+n • d)+d)*conj (derivative q d (a+n • d)) = _ at he
    have hh := unit_conj_cancel (derivative_norm_one q hq d (a+n • d)) he
    rw [progression_step,ih (by omega)] at hh
    rw [hh,pow_succ]
    ring

/-- No global polynomial representation is assumed. The whole progression is
checked to lie in the local domain, including the intermediate cube vertices. -/
theorem local_quadratic_progression_formula {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (a d : G) {N : ℕ} (hR : ∀ n ≤ N, a+n • d ∈ R) :
    ∀ n ≤ N, q (a+n • d) = q a*(derivative q d a)^n*
      (derivative (derivative q d) d a)^(n.choose 2) := by
  have hs (n : ℕ) (hn : n < N) : q (a+(n+1) • d) =
      q (a+n • d)*(derivative q d a*(derivative (derivative q d) d a)^n) := by
    have he : q ((a+n • d)+d)*conj (q (a+n • d)) = derivative q d (a+n • d) := rfl
    have hh := unit_conj_cancel (hq (a+n • d)) he
    rw [progression_step,local_first_derivative_formula hq hquad a d hR n (by omega)] at hh
    simpa only [mul_comm] using hh
  simpa only [zero_nsmul,add_zero] using binomial_sequence_formula
    (fun n ↦ q (a+n • d)) (derivative q d a) (derivative (derivative q d) d a) hs

lemma unit_power_oscillation (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z^n-1‖ ≤ (n : ℝ)*‖z-1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hh := (norm_mul_sub_one_le (by simp only [norm_pow,hz,one_pow] : ‖z^n‖ = 1) (w := z)).trans
      (add_le_add ih le_rfl)
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

/-- A useful flattening criterion: control of the first two multiplicative
derivatives controls every value along the local progression. -/
theorem local_quadratic_progression_oscillation {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (a d : G) {N : ℕ} (hR : ∀ n ≤ N, a+n • d ∈ R) {n : ℕ} (hn : n ≤ N) :
    ‖q (a+n • d)-q a‖ ≤ (n : ℝ)*‖derivative q d a-1‖+
      (n.choose 2 : ℝ)*‖derivative (derivative q d) d a-1‖ := by
  rw [local_quadratic_progression_formula hq hquad a d hR n hn]
  have he : q a*(derivative q d a)^n*(derivative (derivative q d) d a)^(n.choose 2)-q a =
      q a*((derivative q d a)^n*(derivative (derivative q d) d a)^(n.choose 2)-1) := by ring
  rw [he,norm_mul,hq,one_mul]
  have hu := derivative_norm_one q hq d a
  have hv := derivative_norm_one (derivative q d) (derivative_norm_one q hq d) d a
  exact (norm_mul_sub_one_le (by simp only [norm_pow,hu,one_pow])).trans
    (add_le_add (unit_power_oscillation _ hu n) (unit_power_oscillation _ hv (n.choose 2)))

#print axioms local_quadratic_progression_formula
#print axioms local_quadratic_progression_oscillation
end Erdos3LocalQuadraticProgressions
