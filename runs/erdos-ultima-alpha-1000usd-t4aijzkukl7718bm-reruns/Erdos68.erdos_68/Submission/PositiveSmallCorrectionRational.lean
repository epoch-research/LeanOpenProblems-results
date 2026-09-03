import FormalConjecturesUtil

/-!
# A positive, squared-factorial-small correction with rational total

This is an auxiliary comparison, not a disproof of Erdős 68. In original
indices n ≥ 2, the terms are

    1/n! + (4*n^2-3)/(2*n+1)!.

Their sum is 5/6, even though the correction is positive and becomes
negligible after multiplication by (n!)². Thus positivity and this analytic
decay condition do not by themselves establish irrationality. The terms
are not reciprocals of the integers n!-1.
-/

namespace PositiveSmallCorrectionRational

open Filter
open scoped Topology

noncomputable def facTerm (n : ℕ) : ℝ := 1 / (n.factorial : ℝ)

noncomputable def blockTerm (n : ℕ) : ℝ := (n + 2 : ℝ) / (n + 4).factorial

noncomputable def correction (n : ℕ) : ℝ :=
  (4 * (n + 2 : ℝ)^2 - 3) / (2 * (n + 2) + 1).factorial

noncomputable def term (n : ℕ) : ℝ := facTerm (n + 2) + correction n

lemma summable_facTerm : Summable facTerm := by
  simpa only [facTerm, one_pow] using Real.summable_pow_div_factorial 1

lemma summable_facTerm_shift (k : ℕ) : Summable (fun n => facTerm (n + k)) :=
  (summable_nat_add_iff k).mpr summable_facTerm

lemma blockTerm_eq (n : ℕ) :
    blockTerm n = facTerm (n + 3) - 2 * facTerm (n + 4) := by
  have hF : ((n + 3).factorial : ℝ) ≠ 0 := by positivity
  have hN : (n + 4 : ℝ) ≠ 0 := by positivity
  have hf : ((n + 4).factorial : ℝ) = (n + 4) * (n + 3).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 3)
  unfold blockTerm facTerm
  rw [hf]
  field_simp
  ring

lemma summable_blockTerm : Summable blockTerm := by
  change Summable (fun n => blockTerm n)
  simp_rw [blockTerm_eq]
  exact (summable_facTerm_shift 3).sub ((summable_facTerm_shift 4).mul_left 2)

lemma correction_eq_blocks (n : ℕ) :
    correction n = blockTerm (2 * n) + blockTerm (2 * n + 1) := by
  have hF : ((2 * n + 4).factorial : ℝ) ≠ 0 := by positivity
  have hN : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have hf : ((2 * n + 5).factorial : ℝ) =
      (2 * (n : ℝ) + 5) * (2 * n + 4).factorial := by
    exact_mod_cast Nat.factorial_succ (2 * n + 4)
  unfold correction blockTerm
  rw [show 2 * (n + 2) + 1 = 2 * n + 5 by omega,
    show 2 * n + 1 + 4 = 2 * n + 5 by omega, hf]
  push_cast
  field_simp
  ring

lemma summable_blocks_even : Summable (fun n => blockTerm (2 * n)) := by
  exact summable_blockTerm.comp_injective (by intro a b h; omega)

lemma summable_blocks_odd : Summable (fun n => blockTerm (2 * n + 1)) := by
  exact summable_blockTerm.comp_injective (by intro a b h; simp only at h; omega)

lemma summable_correction : Summable correction := by
  change Summable (fun n => correction n)
  simp_rw [correction_eq_blocks]
  exact summable_blocks_even.add summable_blocks_odd

lemma summable_term : Summable term :=
  (summable_facTerm_shift 2).add summable_correction

lemma tsum_correction : (∑' n, correction n) = ∑' n, blockTerm n := by
  simp_rw [correction_eq_blocks]
  rw [summable_blocks_even.tsum_add summable_blocks_odd]
  exact tsum_even_add_odd summable_blocks_even summable_blocks_odd

/-- A rational total for this different positive reciprocal-factorial perturbation. -/
theorem tsum_term : (∑' n, term n) = 5 / 6 := by
  have h2 := summable_facTerm.sum_add_tsum_nat_add 2
  have h3 := summable_facTerm.sum_add_tsum_nat_add 3
  have h4 := summable_facTerm.sum_add_tsum_nat_add 4
  have hs2 : (∑ k ∈ Finset.range 2, facTerm k) = 2 := by
    norm_num [Finset.sum_range_succ, facTerm, Nat.factorial]
  have hs3 : (∑ k ∈ Finset.range 3, facTerm k) = 5 / 2 := by
    norm_num [Finset.sum_range_succ, facTerm, Nat.factorial]
  have hs4 : (∑ k ∈ Finset.range 4, facTerm k) = 8 / 3 := by
    norm_num [Finset.sum_range_succ, facTerm, Nat.factorial]
  rw [hs2] at h2
  rw [hs3] at h3
  rw [hs4] at h4
  have hb : (∑' n, blockTerm n) =
      (∑' n, facTerm (n + 3)) - 2 * ∑' n, facTerm (n + 4) := by
    simp_rw [blockTerm_eq]
    rw [(summable_facTerm_shift 3).tsum_sub
      ((summable_facTerm_shift 4).mul_left 2), tsum_mul_left]
  unfold term
  rw [(summable_facTerm_shift 2).tsum_add summable_correction,
    tsum_correction, hb]
  linarith

lemma correction_pos (n : ℕ) : 0 < correction n := by
  unfold correction
  apply div_pos _ (by positivity)
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma term_gt_reciprocal_factorial (n : ℕ) :
    1 / ((n + 2).factorial : ℝ) < term n := by
  exact lt_add_of_pos_right _ (correction_pos n)

lemma central_factorial_lower (n : ℕ) :
    4^n * (n.factorial : ℝ)^2 ≤ (2 * n + 1).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hf : ((2 * (n + 1) + 1).factorial : ℝ) =
        (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2) * (2 * n + 1).factorial := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hf, Nat.factorial_succ, pow_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := by positivity
    have hpoly : 4 * (n + 1 : ℝ)^2 ≤ (2 * n + 3) * (2 * n + 2) := by
      nlinarith
    calc
      _ = (4 * (n + 1 : ℝ)^2) * (4^n * (n.factorial : ℝ)^2) := by ring
      _ ≤ ((2 * n + 3) * (2 * n + 2)) * (4^n * (n.factorial : ℝ)^2) := by
        gcongr
      _ ≤ ((2 * n + 3) * (2 * n + 2)) * (2 * n + 1).factorial := by
        gcongr
      _ = _ := by ring

lemma normalized_correction_bound (n : ℕ) :
    ((n + 2).factorial : ℝ)^2 * correction n ≤
      4 * (n + 2 : ℝ)^2 * (1 / 4 : ℝ)^(n + 2) := by
  have hF : (0 : ℝ) < (2 * (n + 2) + 1).factorial := by positivity
  have hP : (0 : ℝ) < 4^(n + 2) := by positivity
  have hnum : 0 ≤ 4 * (n + 2 : ℝ)^2 - 3 := (by
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith)
  have hb := central_factorial_lower (n + 2)
  have hratio : ((n + 2).factorial : ℝ)^2 /
      (2 * (n + 2) + 1).factorial ≤ 1 / 4^(n + 2) := by
    apply (div_le_div_iff₀ hF hP).mpr
    nlinarith
  unfold correction
  calc
    _ = (4 * (n + 2 : ℝ)^2 - 3) *
        (((n + 2).factorial : ℝ)^2 / (2 * (n + 2) + 1).factorial) := by ring
    _ ≤ (4 * (n + 2 : ℝ)^2 - 3) * (1 / 4^(n + 2)) := by gcongr
    _ ≤ (4 * (n + 2 : ℝ)^2) * (1 / 4^(n + 2)) := by gcongr; linarith
    _ = _ := by rw [one_div_pow]

/-- The positive correction is o(1/(n!)²), in unshifted indices n ≥ 2. -/
theorem normalized_correction_tendsto :
    Tendsto (fun n => ((n + 2).factorial : ℝ)^2 * correction n) atTop (𝓝 0) := by
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (by norm_num : |(1 / 4 : ℝ)| < 1)).comp (tendsto_add_atTop_nat 2)
  have hu := ht.const_mul (4 : ℝ)
  simp only [mul_zero] at hu
  apply squeeze_zero (fun n => mul_nonneg (sq_nonneg _) (correction_pos n).le)
    normalized_correction_bound
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, mul_assoc] using hu

#print axioms tsum_term
#print axioms normalized_correction_tendsto

end PositiveSmallCorrectionRational
