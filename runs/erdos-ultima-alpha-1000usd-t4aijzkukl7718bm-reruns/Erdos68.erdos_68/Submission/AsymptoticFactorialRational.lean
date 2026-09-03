import Submission.NearFactorialRational

/-!
# A rational comparison with asymptotically factorial denominators

This is a different series, not a proof or disproof of Erdős 68.
The factorial congruence below has a two-index lag. No exact shifted
chain or equality with the original denominators is asserted.
-/

namespace AsymptoticFactorialRational

open Filter
open scoped Topology
open NearFactorialRational (roundCoeff roundDen roundStep roundDen_bounds roundStep_bounds)

def rem : ℕ → ℚ
  | 0 => 1 / (8 : ℕ).factorial
  | n + 1 => roundStep (n + 6).factorial (rem n) (1 / (n + 9).factorial)

def coeff (n : ℕ) : ℤ :=
  roundCoeff (n + 6).factorial (rem n) (1 / (n + 9).factorial)

def denom (n : ℕ) : ℤ := coeff n * (n + 6).factorial - 1

lemma factorial_step_bound (n : ℕ) :
    (1 / (n + 9).factorial : ℚ) +
        (n + 6).factorial * ((1 + 4 / (n + 8)) / (n + 8).factorial : ℚ) ^ 2 ≤
      (1 + 4 / (n + 9)) / (n + 9).factorial := by
  have hF : (0 : ℚ) < (n + 6).factorial := by positivity
  have hn : (0 : ℚ) ≤ n := by positivity
  have h7 : ((n + 7).factorial : ℚ) = (n + 7) * (n + 6).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 6)
  have h8 : ((n + 8).factorial : ℚ) = (n + 8) * (n + 7).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 7)
  have h9 : ((n + 9).factorial : ℚ) = (n + 9) * (n + 8).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 8)
  rw [h9, h8, h7]
  field_simp
  nlinarith [sq_nonneg ((n : ℚ) ^ 2), pow_nonneg hn 3]

lemma rem_bounds (n : ℕ) :
    (1 / (n + 8).factorial : ℚ) ≤ rem n ∧
      rem n ≤ (1 + 4 / (n + 8)) / (n + 8).factorial := by
  induction n with
  | zero => norm_num [rem]
  | succ n ih =>
    have hA : (0 : ℚ) < (n + 6).factorial := by positivity
    have hb : (0 : ℚ) < 1 / (n + 9).factorial := by positivity
    have hbr : (1 / (n + 9).factorial : ℚ) < rem n := by
      apply lt_of_lt_of_le _ ih.1
      apply one_div_lt_one_div_of_lt (by positivity)
      exact_mod_cast Nat.factorial_lt_of_lt (by omega : 1 ≤ n + 8)
        (by omega : n + 8 < n + 9)
    obtain ⟨hl, hu⟩ := roundStep_bounds hA hb hbr
    constructor
    · simpa only [rem, Nat.add_assoc, Nat.reduceAdd] using hl.le
    · have hr : 0 < rem n := lt_of_lt_of_le (by positivity) ih.1
      have hs : rem n ^ 2 ≤ ((1 + 4 / (n + 8)) / (n + 8).factorial : ℚ) ^ 2 := by
        nlinarith [ih.2]
      have hh := mul_le_mul_of_nonneg_left hs hA.le
      have hf := factorial_step_bound n
      simp only [rem, Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one]
      have he : (n : ℚ) + 1 + 8 = n + 9 := by ring
      rw [he]
      linarith

lemma rem_pos (n : ℕ) : 0 < rem n :=
  lt_of_lt_of_le (by positivity) (rem_bounds n).1

lemma base_lt_rem (n : ℕ) : (1 / (n + 9).factorial : ℚ) < rem n := by
  apply lt_of_lt_of_le _ (rem_bounds n).1
  apply one_div_lt_one_div_of_lt (by positivity)
  exact_mod_cast Nat.factorial_lt_of_lt (by omega : 1 ≤ n + 8)
    (by omega : n + 8 < n + 9)

lemma cast_denom (n : ℕ) : (denom n : ℚ) =
    roundDen (n + 6).factorial (rem n) (1 / (n + 9).factorial) := by
  simp [denom, coeff, roundDen]

lemma denom_pos (n : ℕ) : 0 < denom n := by
  have hd := (roundDen_bounds (r := rem n) (b := 1 / (n + 9).factorial)
    (by positivity : (0 : ℚ) < (n + 6).factorial)).1
  rw [← cast_denom n] at hd
  have hp : (0 : ℚ) < denom n :=
    (one_div_pos.mpr (sub_pos.mpr (base_lt_rem n))).trans hd
  exact_mod_cast hp

lemma rem_sub_succ (n : ℕ) : rem n - rem (n + 1) = 1 / (denom n : ℚ) := by
  simp only [rem, roundStep, ← cast_denom]
  ring

lemma rem_le_two (n : ℕ) : rem n ≤ 2 / (n + 8).factorial := by
  apply (rem_bounds n).2.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hn : (0 : ℚ) ≤ n := by positivity
  have h : (4 : ℚ) / (n + 8) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < n + 8)).mpr
    linarith
  linarith

lemma rem_tendsto : Tendsto (fun n => (rem n : ℝ)) atTop (𝓝 0) := by
  have hf : Tendsto (fun n => 1 / ((n + 8).factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 8))
  have htwo : Tendsto (fun n => (2 : ℝ) / (n + 8).factorial) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using hf.const_mul 2
  apply squeeze_zero (fun n => (show (0 : ℝ) < rem n by exact_mod_cast rem_pos n).le)
    (fun n => ?_) htwo
  have h := (Rat.cast_le (K := ℝ)).mpr (rem_le_two n)
  push_cast at h
  exact h

lemma partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (denom k : ℝ)) =
      1 / (8 : ℕ).factorial - (rem n : ℝ) := by
  induction n with
  | zero => norm_num [rem]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (rem n : ℝ) - rem (n + 1) = 1 / (denom n : ℝ) := by
      exact_mod_cast rem_sub_succ n
    linarith

lemma hasSum_reciprocal :
    HasSum (fun n => 1 / (denom n : ℝ)) (1 / (8 : ℕ).factorial) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    have h : (0 : ℝ) < denom n := by exact_mod_cast denom_pos n
    positivity) _).mpr
  simpa only [partial_sum, sub_zero] using
    (tendsto_const_nhds (x := (1 / ((8 : ℕ).factorial : ℝ)))).sub rem_tendsto

lemma factorial_dvd_denom_add_one (n : ℕ) :
    ((n + 6).factorial : ℤ) ∣ denom n + 1 := by
  refine ⟨coeff n, ?_⟩
  simp only [denom, sub_add_cancel]
  ring

lemma scaled_denom_bounds (n : ℕ) :
    (n + 4 : ℚ) * (n + 8).factorial < (n + 8) * (denom n : ℚ) ∧
      (n + 8 : ℚ) * denom n ≤ (n + 10) * (n + 8).factorial := by
  have hA : (0 : ℚ) < (n + 6).factorial := by positivity
  have hF : (0 : ℚ) < (n + 8).factorial := by positivity
  have hn : (0 : ℚ) ≤ n := by positivity
  have h7 : ((n + 7).factorial : ℚ) = (n + 7) * (n + 6).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 6)
  have h8 : ((n + 8).factorial : ℚ) = (n + 8) * (n + 7).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 7)
  have h9 : ((n + 9).factorial : ℚ) = (n + 9) * (n + 8).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 8)
  obtain ⟨hd, hu⟩ := roundDen_bounds (r := rem n) (b := 1 / (n + 9).factorial) hA
  rw [← cast_denom n] at hd hu
  have hpos : (0 : ℚ) < rem n - 1 / (n + 9).factorial :=
    sub_pos.mpr (base_lt_rem n)
  constructor
  · have hsmall : rem n - 1 / (n + 9).factorial <
        ((1 + 4 / (n + 8)) / (n + 8).factorial : ℚ) := by
      have hb : (0 : ℚ) < 1 / (n + 9).factorial := by positivity
      linarith [(rem_bounds n).2]
    have hi := (one_div_lt_one_div_of_lt hpos hsmall).trans hd
    have hid : (1 / ((1 + 4 / (n + 8)) / (n + 8).factorial) : ℚ) =
        (n + 8) * (n + 8).factorial / (n + 12) := by
      field_simp
      ring
    rw [hid] at hi
    have hi' := (div_lt_iff₀ (by positivity : (0 : ℚ) < n + 12)).mp hi
    have hm := mul_lt_mul_of_pos_left hi' (by positivity : (0 : ℚ) < n + 8)
    apply (mul_lt_mul_iff_right₀ (by positivity : (0 : ℚ) < n + 12)).mp
    nlinarith
  · have hid : (1 / (n + 8).factorial - 1 / (n + 9).factorial : ℚ) =
        1 / ((n + 9) * (n + 8).factorial / (n + 8)) := by
      rw [h9]
      field_simp
      ring
    have hlo : (1 / ((n + 9) * (n + 8).factorial / (n + 8)) : ℚ) ≤
        rem n - 1 / (n + 9).factorial := by
      rw [← hid]
      linarith [(rem_bounds n).1]
    have hup := one_div_le_one_div_of_le (by positivity) hlo
    rw [one_div_one_div] at hup
    have hd' : (denom n : ℚ) ≤
        (n + 9) * (n + 8).factorial / (n + 8) + (n + 6).factorial := by
      linarith
    have hm := mul_le_mul_of_nonneg_left hd' (by positivity : (0 : ℚ) ≤ n + 8)
    have hc : (n + 8 : ℚ) *
        ((n + 9) * (n + 8).factorial / (n + 8) + (n + 6).factorial) =
        (n + 9) * (n + 8).factorial + (n + 8) * (n + 6).factorial := by
      field_simp
    rw [hc] at hm
    have hAF : (n + 8 : ℚ) * (n + 6).factorial ≤ (n + 8).factorial := by
      rw [h8, h7]
      have h : (1 : ℚ) ≤ n + 7 := by linarith
      calc
        (n + 8 : ℚ) * (n + 6).factorial =
            (n + 8) * (1 * (n + 6).factorial) := by ring
        _ ≤ (n + 8) * ((n + 7) * (n + 6).factorial) := by gcongr
    nlinarith

lemma ratio_bounds (n : ℕ) :
    1 - 4 / (n + 8 : ℝ) ≤ (denom n : ℝ) / (n + 8).factorial ∧
      (denom n : ℝ) / (n + 8).factorial ≤ 1 + 2 / (n + 8 : ℝ) := by
  have hf : (0 : ℝ) < (n + 8).factorial := by positivity
  have hn : (0 : ℝ) < n + 8 := by positivity
  have hl : (n + 4 : ℝ) * (n + 8).factorial < (n + 8) * denom n := by
    exact_mod_cast (scaled_denom_bounds n).1
  have hu : (n + 8 : ℝ) * denom n ≤ (n + 10) * (n + 8).factorial := by
    exact_mod_cast (scaled_denom_bounds n).2
  constructor
  · apply le_of_lt
    apply (lt_div_iff₀ hf).mpr
    apply (mul_lt_mul_iff_right₀ hn).mp
    have he : (n + 8 : ℝ) * ((1 - 4 / (n + 8)) * (n + 8).factorial) =
        (n + 4) * (n + 8).factorial := by
      field_simp
      ring
    rw [he]
    exact hl
  · apply (div_le_iff₀ hf).mpr
    apply (mul_le_mul_iff_right₀ hn).mp
    have he : (n + 8 : ℝ) * ((1 + 2 / (n + 8)) * (n + 8).factorial) =
        (n + 10) * (n + 8).factorial := by
      field_simp
      ring
    rw [he]
    exact hu

lemma ratio_tendsto :
    Tendsto (fun n => (denom n : ℝ) / (n + 8).factorial) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => 1 / (n + 8 : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      h.comp (tendsto_add_atTop_nat 8)
  have hl : Tendsto (fun n : ℕ => 1 - 4 / (n + 8 : ℝ)) atTop (𝓝 1) := by
    simpa only [mul_one_div, mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul 4)
  have hu : Tendsto (fun n : ℕ => 1 + 2 / (n + 8 : ℝ)) atTop (𝓝 1) := by
    simpa only [mul_one_div, mul_zero, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    (fun n => (ratio_bounds n).1) (fun n => (ratio_bounds n).2)

def natDenom (n : ℕ) : ℕ := (denom n).toNat

lemma cast_natDenom_int (n : ℕ) : (natDenom n : ℤ) = denom n :=
  Int.toNat_of_nonneg (denom_pos n).le

lemma cast_natDenom_real (n : ℕ) : (natDenom n : ℝ) = (denom n : ℝ) := by
  exact_mod_cast cast_natDenom_int n

/-- A rational comparison only: the congruence is two factorial indices
behind the asymptotic denominator, and the denominators are not n!-1. -/
theorem exists_rational_asymptotic_factorial_series :
    ∃ d : ℕ → ℕ,
      (∀ n, 0 < d n ∧ (n + 6).factorial ∣ d n + 1) ∧
      Tendsto (fun n => (d n : ℝ) / (n + 8).factorial) atTop (𝓝 1) ∧
      (∑' n : ℕ, 1 / (d n : ℝ)) = 1 / (8 : ℕ).factorial := by
  refine ⟨natDenom, ?_, ?_, ?_⟩
  · intro n
    have hp := denom_pos n
    have hd := factorial_dvd_denom_add_one n
    rw [← cast_natDenom_int n] at hp hd
    constructor
    · exact_mod_cast hp
    · exact_mod_cast hd
  · simpa only [cast_natDenom_real] using ratio_tendsto
  · simpa only [cast_natDenom_real] using hasSum_reciprocal.tsum_eq

lemma first_denominator : natDenom 0 = 46079 := by
  norm_num [natDenom, denom, coeff, roundCoeff, rem]
  rfl

end AsymptoticFactorialRational

#print axioms AsymptoticFactorialRational.exists_rational_asymptotic_factorial_series
#print axioms AsymptoticFactorialRational.ratio_bounds
#print axioms AsymptoticFactorialRational.first_denominator
