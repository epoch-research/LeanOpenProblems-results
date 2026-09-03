import Submission.Explore

/-!
A harmonic-weighted cancellation consequence of the dyadic comparison identity.
This controls only the signed contribution of the non-between event, not the
full largest-prime-factor comparison and not its natural density.
-/

namespace Erdos371

open Finset Filter
open scoped Topology

private lemma sum_pairs_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range N, (f (2 * k + 2) + f (2 * k + 3))) =
      ∑ k ∈ range (2 * N), f (k + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        sum_range_succ, sum_range_succ]
      simp only [show 2 * N + 1 + 2 = 2 * N + 3 by omega]
      ring

private lemma dyadic_block_difference (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range N, f (k + 1)) -
        (∑ k ∈ range N, (f (2 * k + 2) + f (2 * k + 3))) =
      f 1 - ∑ k ∈ range (N + 1), f (N + k + 1) := by
  rw [sum_pairs_shift]
  have h₁ := sum_range_succ' (fun k => f (k + 1)) (2 * N)
  have h₂ := sum_range_add (fun k => f (k + 1)) N (N + 1)
  simp only [show N + (N + 1) = 2 * N + 1 by omega] at h₂
  simp only [show ∀ k : ℕ, k + 1 + 1 = k + 2 by omega, zero_add] at h₁
  linarith

private lemma reciprocal_dyadic_gap (x : ℝ) (hx : 0 < x) :
    0 ≤ 1 / (2 * x) - 1 / (2 * x + 1) ∧
      1 / (2 * x) - 1 / (2 * x + 1) ≤ 1 / x - 1 / (x + 1) := by
  have h₂ : 0 < 2 * x := by positivity
  have h₃ : 0 < 2 * x + 1 := by positivity
  have h₄ : 0 < x + 1 := by positivity
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le h₂ (by linarith))
  · calc
      1 / (2 * x) - 1 / (2 * x + 1) = 1 / ((2 * x) * (2 * x + 1)) := by
        field_simp
        <;> ring
      _ ≤ 1 / (x * (x + 1)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg x])
      _ = 1 / x - 1 / (x + 1) := by
        field_simp
        <;> ring

private lemma reciprocal_gap_sum (N : ℕ) :
    (∑ k ∈ range N, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

/-- A bounded sequence has uniformly bounded harmonic sums of this dyadic
coboundary. No arithmetic hypothesis on the sequence is needed. -/
theorem harmonic_dyadic_coboundary_bound (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    |∑ k ∈ range N,
      (f (k + 1) - (f (2 * k + 2) + f (2 * k + 3)) / 2) / ((k : ℝ) + 1)| ≤ 3 := by
  let w : ℕ → ℝ := fun n => f n / n
  let err : ℕ → ℝ := fun k => f (2 * k + 3) *
    (1 / (2 * ((k : ℝ) + 1) + 1) - 1 / (2 * ((k : ℝ) + 1)))
  have hterm (k : ℕ) :
      (f (k + 1) - (f (2 * k + 2) + f (2 * k + 3)) / 2) / ((k : ℝ) + 1) =
        w (k + 1) - (w (2 * k + 2) + w (2 * k + 3)) + err k := by
    dsimp [w, err]
    push_cast
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk' : 2 * (k : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    <;> ring
  have herr (k : ℕ) : |err k| ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
    have hgap := reciprocal_dyadic_gap ((k : ℝ) + 1) (by positivity)
    dsimp [err]
    rw [abs_mul, abs_sub_comm, abs_of_nonneg hgap.1]
    have hm := mul_le_mul_of_nonneg_right (hf (2 * k + 3)) hgap.1
    rw [one_mul] at hm
    exact hm.trans (by convert hgap.2 using 1 <;> ring)
  have hsumerr : |∑ k ∈ range N, err k| ≤ 1 := by
    calc
      |∑ k ∈ range N, err k| ≤ ∑ k ∈ range N, |err k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range N, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) :=
        sum_le_sum (fun k _ => herr k)
      _ = 1 - 1 / ((N : ℝ) + 1) := reciprocal_gap_sum N
      _ ≤ 1 := sub_le_self _ (by positivity)
  have htail : |∑ k ∈ range (N + 1), w (N + k + 1)| ≤ 1 := by
    calc
      |∑ k ∈ range (N + 1), w (N + k + 1)| ≤
          ∑ k ∈ range (N + 1), |w (N + k + 1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range (N + 1), (1 / ((N : ℝ) + 1)) := by
        apply sum_le_sum
        intro k hk
        dsimp [w]
        rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (N + k + 1) : (0 : ℝ) ≤ (N + k + 1 : ℕ))]
        calc
          |f (N + k + 1)| / (N + k + 1 : ℕ) ≤ 1 / (N + k + 1 : ℕ) :=
            div_le_div_of_nonneg_right (hf _) (Nat.cast_nonneg _)
          _ ≤ 1 / ((N : ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      _ = 1 := by
        simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        have hN : (N : ℝ) + 1 ≠ 0 := by positivity
        field_simp
  simp_rw [hterm]
  rw [sum_add_distrib, sum_sub_distrib, dyadic_block_difference]
  have hw : |w 1| ≤ 1 := by simpa [w] using hf 1
  calc
    |w 1 - (∑ k ∈ range (N + 1), w (N + k + 1)) + ∑ k ∈ range N, err k| ≤
        |w 1| + |∑ k ∈ range (N + 1), w (N + k + 1)| + |∑ k ∈ range N, err k| :=
      by
          have h₁ := abs_add_le (w 1 - ∑ k ∈ range (N + 1), w (N + k + 1))
            (∑ k ∈ range N, err k)
          have h₂ := abs_sub (w 1) (∑ k ∈ range (N + 1), w (N + k + 1))
          linarith
    _ ≤ 3 := by linarith

/-- The pointwise dyadic identity also holds at `n = 1`. -/
lemma factorSign_dyadic_positive (n : ℕ) (hn : 0 < n) :
    factorSign (2 * n) + factorSign (2 * n + 1) =
      if factorBetween n then 2 * factorSign n else 0 := by
  by_cases h : n = 1
  · subst n
    norm_num [factorSign, predicateSign, factorBetween,
      Nat.prime_two.maxPrimeFac_eq_self, Nat.prime_three.maxPrimeFac_eq_self,
      show Nat.maxPrimeFac 4 = 2 by decide +kernel]
  · exact factorSign_dyadic n (by omega)

noncomputable def nonBetweenHarmonicSum (N : ℕ) : ℝ :=
  ∑ k ∈ range N, if factorBetween (k + 1) then 0 else factorSign (k + 1) / ((k : ℝ) + 1)

/-- Uniform signed cancellation on the non-between event, with harmonic
weights. It is not a bound for the full comparison sum. -/
theorem nonBetweenHarmonicSum_bound (N : ℕ) : |nonBetweenHarmonicSum N| ≤ 3 := by
  have hf (n : ℕ) : |factorSign n| ≤ 1 := by
    unfold factorSign predicateSign
    split_ifs <;> norm_num
  have heq : nonBetweenHarmonicSum N =
      ∑ k ∈ range N,
        (factorSign (k + 1) - (factorSign (2 * k + 2) + factorSign (2 * k + 3)) / 2) /
          ((k : ℝ) + 1) := by
    apply sum_congr rfl
    intro k hk
    have hd := factorSign_dyadic_positive (k + 1) (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      show 2 * k + 2 + 1 = 2 * k + 3 by omega] at hd
    rw [hd]
    split_ifs <;> ring
  rw [heq]
  exact harmonic_dyadic_coboundary_bound factorSign hf N

/-- The non-between signed contribution has zero logarithmic mean. This
statement concerns only that subevent; it does not assert a logarithmic or
natural density for all rising comparisons. -/
theorem nonBetween_logarithmic_cancellation :
    Tendsto (fun N : ℕ => nonBetweenHarmonicSum N / Real.log ((N : ℝ) + 1))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  apply squeeze_zero_norm (a := fun N : ℕ => 3 / Real.log ((N : ℝ) + 1))
  · intro N
    have hnonneg : 0 ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnonneg]
    exact div_le_div_of_nonneg_right (nonBetweenHarmonicSum_bound N) hnonneg
  · exact tendsto_const_nhds.div_atTop hlog

#print axioms harmonic_dyadic_coboundary_bound
#print axioms nonBetweenHarmonicSum_bound
#print axioms nonBetween_logarithmic_cancellation

end Erdos371
