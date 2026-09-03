import Submission.Records

/-!
# A conditional obstruction from attenuation at logarithmic records

This file proves a sufficient criterion for failure of the eventual lower bound
`2 ^ n ≤ x n`. The substantive hypothesis is an attenuation inequality at all
sufficiently late logarithmically weighted prefix records. No combinatorial or
Ramsey estimate establishing that hypothesis is assumed or proved here.

The finite algebraic estimate explicitly requires `a ≤ t`, so that the factor
`1 - a / t` is nonnegative. The asymptotic criterion supplies this condition
on a tail, uses the cofinal records from `Submission.Records`, and contradicts
an error of size `o(2 ^ n / n)`. Polynomial errors are special cases.
-/

set_option autoImplicit false

namespace RealRecords

open Filter
open scoped Topology

/-- An exact prefix record of the sequence `log (n + 2) * x n / 2 ^ n`. -/
def IsLogarithmicRecord (x : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m ≤ n, Real.log ((m : ℝ) + 2) * x m / (2 : ℝ) ^ m ≤
    Real.log ((n : ℝ) + 2) * x n / (2 : ℝ) ^ n

private lemma log_index_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) := by
  apply Real.log_pos
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- The record predicate is equivalent to the ratio API in
`cofinal_logarithmic_records`; no sign condition on `x` is needed. -/
theorem isLogarithmicRecord_iff {x : ℕ → ℝ} {n : ℕ} :
    IsLogarithmicRecord x n ↔
      ∀ m ≤ n, x m ≤ ((2 : ℝ) ^ m / (2 : ℝ) ^ n) *
        (Real.log ((n : ℝ) + 2) / Real.log ((m : ℝ) + 2)) * x n := by
  unfold IsLogarithmicRecord
  apply forall_congr'
  intro m
  apply forall_congr'
  intro _
  have hpm : 0 < (2 : ℝ) ^ m := by positivity
  have hpn : 0 < (2 : ℝ) ^ n := by positivity
  rw [div_le_div_iff₀ hpm hpn, div_mul_div_comm, div_mul_eq_mul_div,
    le_div_iff₀ (mul_pos hpn (log_index_pos m))]
  constructor <;> intro h <;> nlinarith only [h]

/-- Eventual exponential lower bounds supply cofinally many records of the
precise weighted sequence used in the attenuation hypothesis. -/
theorem cofinal_isLogarithmicRecord {x : ℕ → ℝ}
    (hx : ∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) :
    ∀ N : ℕ, ∃ n ≥ N, IsLogarithmicRecord x n := by
  intro N
  obtain ⟨n, hn, hrec⟩ := cofinal_logarithmic_records hx N
  exact ⟨n, hn, isLogarithmicRecord_iff.mpr hrec⟩

/-- Finite scalar estimate: if the record comparison has slack at most
`a / (2 * t)`, attenuation by `1 - a / t` forces an error at least
`a * X / (2 * t)`. Here `Y` can already include an exponential lag factor. -/
theorem attenuation_error_lower_bound {a t r X Y E : ℝ}
    (ha : 0 < a) (ht : 0 < t) (hat : a ≤ t) (hr : 1 ≤ r)
    (hslack : t * (r - 1) ≤ a / 2) (hX : 0 ≤ X)
    (hrec : Y ≤ r * X) (hatt : X ≤ (1 - a / t) * Y + E) :
    (a / 2) * X ≤ t * E := by
  have hc : 0 ≤ 1 - a / t := by
    exact sub_nonneg.mpr ((div_le_one ht).mpr hat)
  have hcoeff : t * ((1 - a / t) * r) ≤ t - a / 2 := by
    calc
      t * ((1 - a / t) * r) = t * r - a * r := by
        field_simp
      _ ≤ t * r - a := by nlinarith
      _ ≤ t - a / 2 := by linarith
  have hmain : X ≤ ((1 - a / t) * r) * X + E := by
    calc
      X ≤ (1 - a / t) * Y + E := hatt
      _ ≤ (1 - a / t) * (r * X) + E :=
        add_le_add (mul_le_mul_of_nonneg_left hrec hc) le_rfl
      _ = ((1 - a / t) * r) * X + E := by ring
  have hmain' := mul_le_mul_of_nonneg_left hmain ht.le
  have hcoeff' := mul_le_mul_of_nonneg_right hcoeff hX
  nlinarith only [hmain', hcoeff']

/-- Multiplying the recent logarithmic slack by `n + c`, rather than `n`,
still gives a sequence tending to zero, for every fixed real shift `c`. -/
theorem tendsto_logarithmic_recent_slack_shift (j : ℕ) (c : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + c) *
      (Real.log ((n : ℝ) + j + 2) / Real.log ((n : ℝ) + 2) - 1))
      atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ => 1 + c / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop c)
  have h := hratio.mul (tendsto_logarithmic_recent_slack j)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- The logarithmic fixed-lag slack is `o(1/n)` also in backward-index form.
The finitely many indices with `n < j` are immaterial. -/
theorem tendsto_logarithmic_backward_slack (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (Real.log ((n : ℝ) + 2) / Real.log (((n - j : ℕ) : ℝ) + 2) - 1))
      atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat j).mp
  simpa only [Nat.add_sub_cancel_right, Nat.cast_add] using
    tendsto_logarithmic_recent_slack_shift j (j : ℝ)

/-- At one logarithmic record, sufficiently small weight slack turns
attenuation into the explicit lower bound `(a / 2) * x n ≤ n * E`. -/
theorem logarithmic_record_attenuation_lower_bound
    {x : ℕ → ℝ} {n j : ℕ} {a E : ℝ}
    (ha : 0 < a) (hjn : j ≤ n) (han : a ≤ (n : ℝ))
    (hx : 0 ≤ x n) (hrec : IsLogarithmicRecord x n)
    (hslack : (n : ℝ) *
      (Real.log ((n : ℝ) + 2) / Real.log (((n - j : ℕ) : ℝ) + 2) - 1) ≤ a / 2)
    (hatt : x n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * x (n - j) + E) :
    (a / 2) * x n ≤ (n : ℝ) * E := by
  have hnpos : 0 < (n : ℝ) := ha.trans_le han
  have hr : 1 ≤ Real.log ((n : ℝ) + 2) /
      Real.log (((n - j : ℕ) : ℝ) + 2) := by
    apply (le_div_iff₀ (log_index_pos (n - j))).mpr
    simp only [one_mul]
    apply Real.log_le_log (by positivity)
    have hmn : ((n - j : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n j
    linarith
  have hprev := isLogarithmicRecord_iff.mp hrec (n - j) (Nat.sub_le n j)
  have hscaled := mul_le_mul_of_nonneg_left hprev (by positivity : 0 ≤ (2 : ℝ) ^ j)
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - j) * (2 : ℝ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjn]
  have hscaled' : (2 : ℝ) ^ j * x (n - j) ≤
      (Real.log ((n : ℝ) + 2) / Real.log (((n - j : ℕ) : ℝ) + 2)) * x n := by
    convert hscaled using 1
    rw [hpow]
    field_simp
  apply attenuation_error_lower_bound ha hnpos han hr hslack hx hscaled'
  convert hatt using 1
  ring

/-- A finite, quantitatively explicit contradiction at a single record.
There are no limits in the hypotheses of this lemma. -/
theorem logarithmic_record_attenuation_contradiction
    {x : ℕ → ℝ} {n j : ℕ} {a E : ℝ}
    (ha : 0 < a) (hjn : j ≤ n) (han : a ≤ (n : ℝ))
    (hx : (2 : ℝ) ^ n ≤ x n) (hrec : IsLogarithmicRecord x n)
    (hslack : (n : ℝ) *
      (Real.log ((n : ℝ) + 2) / Real.log (((n - j : ℕ) : ℝ) + 2) - 1) ≤ a / 2)
    (hatt : x n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * x (n - j) + E)
    (herror : (n : ℝ) * E / (2 : ℝ) ^ n < a / 2) : False := by
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have hlower := logarithmic_record_attenuation_lower_bound ha hjn han
    (hpowpos.le.trans hx) hrec hslack hatt
  have hmul := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ a / 2)
  have hupper := (div_lt_iff₀ hpowpos).mp herror
  linarith

/-- Conditional obstruction with an explicit eventual error threshold.
Attenuation is required only at logarithmic prefix records, not at every index.
The lag `j` is arbitrary but fixed (the statement even allows `j = 0`). -/
theorem not_eventually_exp_lower_of_record_attenuation_of_error_bound
    {x e : ℕ → ℝ} {j : ℕ} {a : ℝ} (ha : 0 < a)
    (he : ∀ᶠ n : ℕ in atTop, (n : ℝ) * e n / (2 : ℝ) ^ n < a / 2)
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord x n →
      x n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * x (n - j) + e n) :
    ¬ (∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) := by
  intro hx
  have hslack : ∀ᶠ n : ℕ in atTop, (n : ℝ) *
      (Real.log ((n : ℝ) + 2) / Real.log (((n - j : ℕ) : ℝ) + 2) - 1) < a / 2 :=
    (tendsto_logarithmic_backward_slack j).eventually (gt_mem_nhds (half_pos ha))
  have han : ∀ᶠ n : ℕ in atTop, a ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop a
  have hnotrec : ∀ᶠ n in atTop, ¬ IsLogarithmicRecord x n := by
    filter_upwards [hx, hatt, hslack, he, han, eventually_ge_atTop j]
      with n hxn hattn hslackn hen hann hjn
    intro hrec
    exact logarithmic_record_attenuation_contradiction ha hjn hann hxn hrec
      hslackn.le (hattn hrec) hen
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnotrec
  obtain ⟨n, hn, hrec⟩ := cofinal_isLogarithmicRecord hx N
  exact hN n hn hrec

/-- Main asymptotic sufficient criterion. If `n * e n / 2 ^ n → 0` and all
sufficiently late logarithmic prefix records satisfy fixed-lag attenuation by
`1 - a / n`, for a fixed `a > 0`, then `x n ≥ 2 ^ n` cannot hold eventually.

This is a conditional real-sequence theorem, not an assertion that a given
combinatorial sequence satisfies the attenuation hypothesis. No positivity
assumption on `e` is necessary. Any fixed natural lag is allowed, hence in
particular every `j ≥ 1`. -/
theorem not_eventually_exp_lower_of_record_attenuation
    {x e : ℕ → ℝ} {j : ℕ} {a : ℝ} (ha : 0 < a)
    (he : Tendsto (fun n : ℕ => (n : ℝ) * e n / (2 : ℝ) ^ n) atTop (𝓝 0))
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord x n →
      x n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * x (n - j) + e n) :
    ¬ (∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) := by
  exact not_eventually_exp_lower_of_record_attenuation_of_error_bound ha
    (he.eventually (gt_mem_nhds (half_pos ha))) hatt

/-- A constant times any fixed power of `n` is an admissible error. This
uses mathlib's `tendsto_pow_const_div_const_pow_of_one_lt` at exponent `d + 1`. -/
theorem tendsto_scaled_monomial_error (C : ℝ) (d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (C * (n : ℝ) ^ d) / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt (d + 1)
    (by norm_num : 1 < (2 : ℝ))).const_mul C
  simp only [mul_zero] at h
  convert h using 1
  ext n
  rw [pow_succ]
  ring

/-- Every real polynomial error satisfies the scaled little-oh condition. -/
theorem tendsto_scaled_polynomial_error (p : Polynomial ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * p.eval (n : ℝ) / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial d C =>
      simpa only [Polynomial.eval_monomial] using tendsto_scaled_monomial_error C d
  | add p q hp hq =>
      simpa only [Polynomial.eval_add, mul_add, add_div, add_zero] using hp.add hq

/-- Polynomial-error corollary of the asymptotic criterion. The polynomial
need not be nonnegative; only the stated record-local inequality is required. -/
theorem not_eventually_exp_lower_of_record_attenuation_polynomial
    {x : ℕ → ℝ} {j : ℕ} {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord x n →
      x n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * x (n - j) + p.eval (n : ℝ)) :
    ¬ (∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) := by
  exact not_eventually_exp_lower_of_record_attenuation ha
    (tendsto_scaled_polynomial_error p) hatt

/-- An eventual one-sided polynomial majorant for the error also suffices.
No convergence or lower bound on the error itself is needed in this variant. -/
theorem not_eventually_exp_lower_of_record_attenuation_of_polynomial_bound
    {x e : ℕ → ℝ} {j : ℕ} {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    (he : ∀ᶠ n in atTop, e n ≤ p.eval (n : ℝ))
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord x n →
      x n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * x (n - j) + e n) :
    ¬ (∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) := by
  apply not_eventually_exp_lower_of_record_attenuation_polynomial ha p
  filter_upwards [he, hatt] with n hen hattn
  intro hrec
  exact (hattn hrec).trans (add_le_add le_rfl hen)

end RealRecords

#print axioms RealRecords.isLogarithmicRecord_iff
#print axioms RealRecords.cofinal_isLogarithmicRecord
#print axioms RealRecords.attenuation_error_lower_bound
#print axioms RealRecords.tendsto_logarithmic_recent_slack_shift
#print axioms RealRecords.tendsto_logarithmic_backward_slack
#print axioms RealRecords.logarithmic_record_attenuation_lower_bound
#print axioms RealRecords.logarithmic_record_attenuation_contradiction
#print axioms RealRecords.not_eventually_exp_lower_of_record_attenuation_of_error_bound
#print axioms RealRecords.not_eventually_exp_lower_of_record_attenuation
#print axioms RealRecords.tendsto_scaled_monomial_error
#print axioms RealRecords.tendsto_scaled_polynomial_error
#print axioms RealRecords.not_eventually_exp_lower_of_record_attenuation_polynomial
#print axioms RealRecords.not_eventually_exp_lower_of_record_attenuation_of_polynomial_bound
