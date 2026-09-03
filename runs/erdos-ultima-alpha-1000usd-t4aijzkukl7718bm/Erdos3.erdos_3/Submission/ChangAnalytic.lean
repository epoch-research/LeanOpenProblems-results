import Submission.DissociatedRiesz

/-! Elementary finite log-moment estimates used for Chang's large-spectrum lemma. -/
namespace Erdos3ChangAnalytic
open Finset
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 1000000

lemma expect_re {V : Type*} [Fintype V] (f : V → ℂ) :
    (𝔼 x, f x).re = 𝔼 x, (f x).re :=
  map_expect (Complex.reCLM.toLinearMap.restrictScalars ℚ≥0) f univ

lemma expect_log_le_log_expect {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    (𝔼 x, Real.log (f x)) ≤ Real.log (𝔼 x, f x) := by
  let M := 𝔼 x, f x
  have hM : 0 < M := expect_pos (fun x _ ↦ hf x) univ_nonempty
  have hb (x : V) : Real.log (f x) - Real.log M ≤ f x / M - 1 := by
    rw [← Real.log_div (hf x).ne' hM.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hf x) hM)
  have h := expect_le_expect (s := univ) (fun x _ ↦ hb x)
  rw [expect_sub_distrib, expect_sub_distrib, Fintype.expect_const,
    Fintype.expect_const, ← expect_div, show (𝔼 x, f x) = M from rfl,
    div_self hM.ne'] at h
  linarith

lemma norm_one_add_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < ‖1+z‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he : z = -1 := eq_neg_of_add_eq_zero_right h
  simpa only [he, norm_neg, norm_one, lt_self_iff_false] using hz

lemma log_norm_one_add_lower {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    z.re - ‖z‖^2 ≤ Real.log ‖1+z‖ := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hlog := Complex.norm_log_one_add_sub_self_le hz1
  have hi : (1-‖z‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos_of_lt hz1) (by norm_num)]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg ‖z‖)
  have he := (Complex.abs_re_le_norm (Complex.log (1+z)-z)).trans hlog
  rw [Complex.sub_re, Complex.log_re] at he
  have hl := (abs_le.mp he).1
  nlinarith

lemma log_norm_sq_one_add_lower {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    2*z.re - 2*‖z‖^2 ≤ Real.log (‖1+z‖^2) := by
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [log_norm_one_add_lower hz]

lemma exists_unit_phase {z : ℂ} (hz : z ≠ 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (u*z).re = ‖z‖ := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp only [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self hn]
  · rw [div_mul_eq_mul_div, mul_comm (conj z) z, Complex.mul_conj,
      Complex.div_ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    field_simp

#print axioms expect_log_le_log_expect
#print axioms log_norm_sq_one_add_lower
#print axioms exists_unit_phase
end Erdos3ChangAnalytic
