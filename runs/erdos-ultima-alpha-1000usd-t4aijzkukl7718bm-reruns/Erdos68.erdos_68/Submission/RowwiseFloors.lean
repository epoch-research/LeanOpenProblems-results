import Submission.Development
import Submission.FactorialTailCriterion

/-!
# Rowwise factorial carrying

This auxiliary representation has small positive scaled tails. It does not
settle Erdős 68: the congruence used by the integer-tail descent criterion is
not preserved by this carrying operation.
-/

namespace Erdos68Development

open Filter
open scoped Topology

def scaledRow (N k : ℕ) : ℚ :=
  (N.factorial : ℚ) / ((k + 2).factorial - 1 : ℚ)

def rowFloor (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N - 1), ⌊scaledRow N k⌋

noncomputable def rowTail (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * (∑' k : ℕ, term k) - rowFloor N

lemma cast_scaledRow (N k : ℕ) :
    (scaledRow N k : ℝ) = (N.factorial : ℝ) * term k := by
  simp [scaledRow, term, div_eq_mul_inv]

lemma floor_scaledRow_le (N k : ℕ) :
    (⌊scaledRow N k⌋ : ℝ) ≤ (N.factorial : ℝ) * term k := by
  rw [← cast_scaledRow, ← Rat.floor_cast (α := ℝ)]
  exact Int.floor_le _

lemma floor_scaledRow_ge (N k : ℕ) :
    (N.factorial : ℝ) * term k - 1 ≤ (⌊scaledRow N k⌋ : ℝ) := by
  have h := Int.lt_floor_add_one (scaledRow N k : ℝ)
  rw [Rat.floor_cast, cast_scaledRow] at h
  linarith

lemma scaledRow_zero (N : ℕ) : scaledRow N 0 = N.factorial := by
  norm_num [scaledRow]

lemma rowFloor_le_scaled_partial (N : ℕ) :
    (rowFloor N : ℝ) ≤ (N.factorial : ℝ) *
      ∑ k ∈ Finset.range (N - 1), term k := by
  simp only [rowFloor, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => floor_scaledRow_le N k)

lemma rowFloor_ge_scaled_partial {N : ℕ} (hN : 2 ≤ N) :
    (N.factorial : ℝ) * (∑ k ∈ Finset.range (N - 1), term k) - (N - 2 : ℝ)
      ≤ (rowFloor N : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have ht : term 0 = 1 := by norm_num [term]
  have hs := Finset.sum_le_sum (s := Finset.range n)
    (fun k _ => floor_scaledRow_ge (n + 2) (k + 1))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hs
  simp only [rowFloor, show n + 2 - 1 = n + 1 by omega,
    Finset.sum_range_succ', scaledRow_zero, Int.floor_natCast,
    Int.cast_add, Int.cast_sum, Int.cast_natCast, ht]
  push_cast
  nlinarith

lemma rowTail_pos (N : ℕ) : 0 < rowTail N := by
  have hp := (partial_sum_error (N - 1)).1
  have hf : (0 : ℝ) < N.factorial := by positivity
  have hh := mul_pos hf hp
  have hlo := rowFloor_le_scaled_partial N
  unfold rowTail
  nlinarith

lemma rowTail_small {N : ℕ} (hN : 3 ≤ N) :
    0 < rowTail N ∧ rowTail N < (N : ℝ) - 1 := by
  refine ⟨rowTail_pos N, ?_⟩
  have he := (scaled_partial_sum_error (N - 1)).2
  rw [show N - 1 + 1 = N by omega] at he
  have he' : (N.factorial : ℝ) *
      ((∑' k : ℕ, term k) - ∑ k ∈ Finset.range (N - 1), term k)
        ≤ 3 / (N + 1 : ℝ) := by
    have hh : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      ring
    simpa only [hh] using he
  have hr : (3 : ℝ) / (N + 1) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlo := rowFloor_ge_scaled_partial (by omega : 2 ≤ N)
  unfold rowTail
  nlinarith

def rowCoeff : ℕ → ℤ
  | 0 => rowFloor 0
  | n + 1 => rowFloor (n + 1) - (n + 1 : ℤ) * rowFloor n

lemma scaledRow_succ (N k : ℕ) :
    scaledRow (N + 1) k = (N + 1 : ℚ) * scaledRow N k := by
  simp only [scaledRow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

lemma floor_scaledRow_mul_le (N k : ℕ) :
    (N + 1 : ℤ) * ⌊scaledRow N k⌋ ≤ ⌊scaledRow (N + 1) k⌋ := by
  apply Int.le_floor.mpr
  rw [scaledRow_succ]
  push_cast
  exact mul_le_mul_of_nonneg_left (Int.floor_le _) (by positivity)

lemma floor_scaledRow_nonneg (N k : ℕ) : 0 ≤ ⌊scaledRow N k⌋ := by
  apply Int.floor_nonneg.mpr
  have hr : (0 : ℝ) ≤ (scaledRow N k : ℝ) := by
    rw [cast_scaledRow]
    exact mul_nonneg (by positivity) (term_pos k).le
  exact_mod_cast hr

lemma rowCoeff_nonneg (N : ℕ) : 0 ≤ rowCoeff N := by
  rcases N with _ | _ | n
  · simp [rowCoeff, rowFloor]
  · simp [rowCoeff, rowFloor]
  · have hs := Finset.sum_le_sum (s := Finset.range n)
      (fun k _ => floor_scaledRow_mul_le (n + 1) k)
    simp only [← Finset.mul_sum] at hs
    have hp := floor_scaledRow_nonneg (n + 2) n
    simp only [rowCoeff, rowFloor, Nat.add_sub_cancel,
      Finset.sum_range_succ]
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] at hs hp ⊢
    omega

lemma rowCoeff_partial (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (rowCoeff k : ℝ) / k.factorial) =
      (rowFloor N : ℝ) / N.factorial := by
  induction N with
  | zero => simp [rowCoeff]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [rowCoeff, Int.cast_sub, Int.cast_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma rowFloor_error (N : ℕ) :
    (∑' k : ℕ, term k) - (rowFloor N : ℝ) / N.factorial =
      rowTail N / N.factorial := by
  unfold rowTail
  have hf : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma rowFloor_error_bound (n : ℕ) :
    0 ≤ (∑' k : ℕ, term k) - (rowFloor (n + 3) : ℝ) / (n + 3).factorial ∧
      (∑' k : ℕ, term k) - (rowFloor (n + 3) : ℝ) / (n + 3).factorial ≤
        1 / ((n + 2).factorial : ℝ) := by
  rw [rowFloor_error]
  have hf : (0 : ℝ) < (n + 3).factorial := by positivity
  have ht := rowTail_small (show 3 ≤ n + 3 by omega)
  push_cast at ht
  refine ⟨div_nonneg ht.1.le hf.le, ?_⟩
  calc
    rowTail (n + 3) / (n + 3).factorial ≤
        (n + 3 : ℝ) / (n + 3).factorial := by
      exact div_le_div_of_nonneg_right (by exact le_trans ht.2.le (by linarith)) hf.le
    _ = 1 / ((n + 2).factorial : ℝ) := by
      rw [show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ]
      push_cast
      field_simp
      ring

lemma rowFloor_tendsto : Tendsto (fun N => (rowFloor N : ℝ) / N.factorial)
    atTop (𝓝 (∑' k : ℕ, term k)) := by
  have hb : Tendsto (fun n => 1 / ((n + 2).factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 2))
  have he : Tendsto
      (fun n => (∑' k : ℕ, term k) - (rowFloor (n + 3) : ℝ) / (n + 3).factorial)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => (rowFloor_error_bound n).1)
      (fun n => (rowFloor_error_bound n).2) hb
  apply (tendsto_add_atTop_iff_nat 3).mp
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := (∑' k : ℕ, term k))).sub he

lemma hasSum_rowCoeff : HasSum (fun k => (rowCoeff k : ℝ) / k.factorial)
    (∑' k : ℕ, term k) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k =>
    div_nonneg (by exact_mod_cast rowCoeff_nonneg k) (by positivity)) _).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [rowCoeff_partial] using rowFloor_tendsto

lemma sum_rowCoeff : (∑' k : ℕ, (rowCoeff k : ℝ) / k.factorial) =
    ∑' k : ℕ, term k := hasSum_rowCoeff.tsum_eq

lemma rowCoeff_scaledTail (N : ℕ) :
    FactorialTailCriterion.scaledTail rowCoeff N = rowTail N := by
  rw [FactorialTailCriterion.scaledTail, sum_rowCoeff, rowCoeff_partial, mul_sub,
    mul_div_cancel₀ _ (by positivity : (N.factorial : ℝ) ≠ 0)]
  rfl

lemma rowCoeff_scaledTail_small {N : ℕ} (hN : 3 ≤ N) :
    0 < FactorialTailCriterion.scaledTail rowCoeff N ∧
      FactorialTailCriterion.scaledTail rowCoeff N < (N : ℝ) - 1 := by
  rw [rowCoeff_scaledTail]
  exact rowTail_small hN

/-- The rowwise coefficients fail the Lambert congruence already at index 6. -/
lemma rowFloor_first_congruence_failure :
    rowFloor 5 = 150 ∧ rowFloor 6 = 902 ∧
      ¬(5 : ℤ) ∣ (rowFloor 6 - 6 * rowFloor 5) - 1 := by
  norm_num [rowFloor, scaledRow, Finset.sum_range_succ, Nat.factorial]

lemma rowCoeff_six : rowCoeff 6 = 2 := by
  change rowFloor 6 - 6 * rowFloor 5 = 2
  rw [rowFloor_first_congruence_failure.1, rowFloor_first_congruence_failure.2.1]
  norm_num

/-- A conditional application only: no eventual congruence has been proved. -/
lemma irrational_of_eventual_rowCoeff_congruence
    (h : ∃ M : ℕ, ∀ n ≥ M, (n : ℤ) ∣ rowCoeff (n + 1) - 1) :
    Irrational (∑' k : ℕ, term k) := by
  obtain ⟨M, hM⟩ := h
  rw [← sum_rowCoeff]
  apply FactorialTailCriterion.irrational_of_small_congruent_tails rowCoeff (max M 3)
  · intro n hn
    exact hM n ((le_max_left _ _).trans hn)
  · intro n hn
    exact rowCoeff_scaledTail_small ((le_max_right _ _).trans hn)

#print axioms sum_rowCoeff
#print axioms rowCoeff_scaledTail_small
#print axioms rowTail_small
#print axioms rowFloor_first_congruence_failure

end Erdos68Development
