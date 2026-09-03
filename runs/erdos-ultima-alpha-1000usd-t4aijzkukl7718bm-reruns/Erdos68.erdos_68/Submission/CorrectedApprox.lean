import Submission.Development

/-!
# Strict rational upper approximations

The correction `1/(N*N!)` gives strict upper approximations for `N >= 3`.
This is an auxiliary development, not a proof of Erdős 68.
-/

namespace Erdos68Development

open Filter
open scoped Topology

/-- `S_N + 1/(N*N!)`, with `N=n+3`. -/
def correctedApprox (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 2), 1 / ((k + 2).factorial - 1 : ℚ)) +
    1 / ((n + 3 : ℚ) * (n + 3).factorial)

lemma cast_correctedApprox (n : ℕ) : (correctedApprox n : ℝ) =
    (∑ k ∈ Finset.range (n + 2), term k) +
      1 / ((n + 3 : ℝ) * (n + 3).factorial) := by
  simp [correctedApprox, term]

lemma correctedApprox_gap (n : ℕ) :
    (correctedApprox n : ℝ) - correctedApprox (n + 1) =
      (((n + 4 : ℝ) * (n + 3).factorial - 1) - (n + 3) * (n + 4)) /
        ((n + 3) * (n + 4)^2 * (n + 3).factorial *
          ((n + 4) * (n + 3).factorial - 1)) := by
  have hf : ((n + 3).factorial : ℝ) ≠ 0 := by positivity
  have hn3 : (n + 3 : ℝ) ≠ 0 := by positivity
  have hn4 : (n + 4 : ℝ) ≠ 0 := by positivity
  have hd : (n + 4 : ℝ) * (n + 3).factorial - 1 ≠ 0 := by
    have := denom_pos (n + 2)
    rw [show n + 2 + 2 = (n + 3) + 1 by omega, Nat.factorial_succ (n + 3)] at this
    push_cast at this
    convert this.ne' using 1; ring
  rw [cast_correctedApprox, cast_correctedApprox,
    show n + 1 + 2 = (n + 2) + 1 by omega, Finset.sum_range_succ term (n + 2)]
  unfold term
  rw [show n + 2 + 2 = (n + 3) + 1 by omega,
    show n + 1 + 3 = (n + 3) + 1 by omega, Nat.factorial_succ (n + 3)]
  push_cast
  rw [show (↑n + 3 + 1 : ℝ) = ↑n + 4 by ring,
    show (↑n + 1 + 3 : ℝ) = ↑n + 4 by ring]
  have hd' : ((n + 3).factorial : ℝ) * (n + 4) - 1 ≠ 0 := by
    simpa only [mul_comm] using hd
  field_simp [hf, hn3, hn4, hd, hd']
  ring

lemma factorial_ge_twice_add_three (n : ℕ) :
    2 * (n + 3 : ℝ) ≤ (n + 3).factorial := by
  rw [show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ (n + 2)]
  push_cast
  have h := mul_le_mul_of_nonneg_left (factorial_ge_two n)
    (show (0 : ℝ) ≤ n + 3 by positivity)
  nlinarith

lemma correctedApprox_strictAnti : StrictAnti (fun n => (correctedApprox n : ℝ)) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  apply sub_pos.mp
  rw [correctedApprox_gap]
  have hf := factorial_ge_twice_add_three n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ n + 4 by positivity)
  apply div_pos
  · nlinarith
  · apply mul_pos
    · positivity
    · nlinarith

lemma correctedApprox_tendsto : Tendsto (fun n => (correctedApprox n : ℝ))
    atTop (𝓝 (∑' k : ℕ, term k)) := by
  have hf : Tendsto (fun n => 1 / ((n + 3).factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 3))
  have hc : Tendsto (fun n : ℕ => 1 / ((n + 3 : ℝ) * (n + 3).factorial))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) _ hf
    intro n
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) (n + 3).factorial]
  have hs := summable_term.tendsto_sum_tsum_nat.comp (tendsto_add_atTop_nat 2)
  simpa only [cast_correctedApprox, add_zero] using hs.add hc

lemma sum_lt_correctedApprox (n : ℕ) :
    (∑' k : ℕ, term k) < (correctedApprox n : ℝ) := by
  exact (correctedApprox_strictAnti.antitone.le_of_tendsto correctedApprox_tendsto (n + 1)).trans_lt
    (correctedApprox_strictAnti (by omega : n < n + 1))

lemma correctedApprox_error (n : ℕ) :
    0 < (correctedApprox n : ℝ) - ∑' k : ℕ, term k ∧
      (correctedApprox n : ℝ) - ∑' k : ℕ, term k <
        1 / ((n + 3) * (n + 4) * ((n + 3).factorial : ℝ)) := by
  refine ⟨sub_pos.mpr (sum_lt_correctedApprox n), ?_⟩
  have ht := (partial_sum_error (n + 2 + 1)).1
  rw [Finset.sum_range_succ] at ht
  rw [cast_correctedApprox]
  have hterm : 1 / ((n + 4 : ℝ) * (n + 3).factorial) < term (n + 2) := by
    unfold term
    rw [show n + 2 + 2 = (n + 3) + 1 by omega, Nat.factorial_succ (n + 3)]
    push_cast
    apply one_div_lt_one_div_of_lt
    · have h := denom_pos (n + 2)
      rw [show n + 2 + 2 = (n + 3) + 1 by omega, Nat.factorial_succ (n + 3)] at h
      push_cast at h
      exact h
    · ring_nf
      norm_num
  have hid : 1 / ((n + 3 : ℝ) * (n + 3).factorial) -
      1 / ((n + 4 : ℝ) * (n + 3).factorial) =
        1 / ((n + 3) * (n + 4) * ((n + 3).factorial : ℝ)) := by
    field_simp
    ring
  linarith

lemma factorial_quad_lower (k : ℕ) :
    4 * (k + 5) * (k + 6) ≤ (k + 5).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 5 = (k + 5) + 1 by omega, Nat.factorial_succ]
    have h := Nat.mul_le_mul_left (k + 6) ih
    have h' : k + 7 ≤ (k + 5) * (k + 6) := by nlinarith
    have h'' := Nat.mul_le_mul_left (4 * (k + 6)) h'
    nlinarith

private lemma scaled_gap_gt_one (x F : ℝ) (hx : 5 ≤ x)
    (hF : 4 * x * (x + 1) ≤ F) :
    1 < ((F - 1) * x * F) *
      (((x + 1) * F - 1 - x * (x + 1)) /
        (x * (x + 1)^2 * F * ((x + 1) * F - 1))) := by
  have hxp : 0 < x := by linarith
  have hxp1 : 0 < x + 1 := by linarith
  have hFp : 0 < F := by nlinarith
  have hF3 : 3 * x ≤ F := by nlinarith
  have hd2 : 2 * x * (x + 1) < (x + 1) * F - 1 := by
    have h := mul_le_mul_of_nonneg_left hF3 hxp1.le
    nlinarith
  have hdp : 0 < (x + 1) * F - 1 := by nlinarith
  have ht : 2 * (x + 1)^2 < F - 1 := by nlinarith
  have hid : ((F - 1) * x * F) *
      (((x + 1) * F - 1 - x * (x + 1)) /
        (x * (x + 1)^2 * F * ((x + 1) * F - 1))) =
      ((F - 1) * ((x + 1) * F - 1 - x * (x + 1))) /
        ((x + 1)^2 * ((x + 1) * F - 1)) := by
    field_simp
  rw [hid]
  apply (one_lt_div (mul_pos (sq_pos_of_pos hxp1) hdp)).mpr
  have hh1 := mul_lt_mul_of_pos_right ht
    (show 0 < (x + 1) * F - 1 - x * (x + 1) by nlinarith)
  have hh2 := mul_lt_mul_of_pos_left hd2 (sq_pos_of_pos hxp1)
  nlinarith

lemma correctedApprox_clearing_lower {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M)
    (hd : denom (n + 1) ∣ M) (hc : (n + 3) * (n + 3).factorial ∣ M) :
    (((n + 3).factorial : ℝ) - 1) * (n + 3) * (n + 3).factorial ≤ M := by
  have hf : ((n + 3).factorial).Coprime (denom (n + 1)) := by
    unfold denom
    rw [show n + 1 + 2 = n + 3 by omega]
    exact (Nat.coprime_self_sub_right (Nat.factorial_pos _)).mpr (Nat.coprime_one_right _)
  have hn' : (n + 3).Coprime (denom (n + 1)) :=
    hf.of_dvd_left (Nat.dvd_factorial (by omega) le_rfl)
  have h := Nat.le_of_dvd hM ((hn'.mul_left hf).mul_dvd_of_dvd_of_dvd hc hd)
  have hdcast : (denom (n + 1) : ℝ) = (n + 3).factorial - 1 := by
    unfold denom
    rw [Nat.cast_sub (Nat.factorial_pos _), Nat.cast_one]
  have h' : ((n + 3) * (n + 3).factorial : ℝ) * (denom (n + 1) : ℝ) ≤ M := by
    exact_mod_cast h
  rw [hdcast] at h'
  nlinarith

/-- Even clearing the last included denominator and the correction denominator is
already too expensive for the elementary positive-integer error argument. -/
lemma correctedApprox_termwise_clearing_error_gt_one {n M : ℕ}
    (hn : 2 ≤ n) (hM : 0 < M) (hd : denom (n + 1) ∣ M)
    (hc : (n + 3) * (n + 3).factorial ∣ M) :
    1 < (M : ℝ) * ((correctedApprox n : ℝ) - ∑' k : ℕ, term k) := by
  have hF : 4 * (n + 3 : ℝ) * (n + 4) ≤ (n + 3).factorial := by
    have h := factorial_quad_lower (n - 2)
    rw [show n - 2 + 5 = n + 3 by omega, show n - 2 + 6 = n + 4 by omega] at h
    exact_mod_cast h
  have hgap := scaled_gap_gt_one (n + 3) (n + 3).factorial (by exact_mod_cast (show 5 ≤ n + 3 by omega)) (by
    simpa only [show (n + 3 : ℝ) + 1 = n + 4 by ring] using hF)
  simp only [show (n + 3 : ℝ) + 1 = n + 4 by ring] at hgap
  rw [← correctedApprox_gap] at hgap
  have hm := correctedApprox_clearing_lower hn hM hd hc
  have hgpos : 0 ≤ (correctedApprox n : ℝ) - correctedApprox (n + 1) :=
    sub_nonneg.mpr (correctedApprox_strictAnti.antitone (by omega))
  calc
    1 < (((n + 3).factorial : ℝ) - 1) * (n + 3) * (n + 3).factorial *
        ((correctedApprox n : ℝ) - correctedApprox (n + 1)) := hgap
    _ ≤ (M : ℝ) * ((correctedApprox n : ℝ) - correctedApprox (n + 1)) :=
      mul_le_mul_of_nonneg_right hm hgpos
    _ < _ := mul_lt_mul_of_pos_left
      (by linarith [sum_lt_correctedApprox (n + 1)]) (by exact_mod_cast hM)

end Erdos68Development

#print axioms Erdos68Development.sum_lt_correctedApprox
#print axioms Erdos68Development.correctedApprox_error

#print axioms Erdos68Development.correctedApprox_termwise_clearing_error_gt_one
