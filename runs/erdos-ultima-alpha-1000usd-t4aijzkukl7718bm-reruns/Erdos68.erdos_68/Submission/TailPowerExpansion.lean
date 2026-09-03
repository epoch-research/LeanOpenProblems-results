import Submission.Development

/-!
Exact finite-order expansions of the tails in Erdos 68. This file is auxiliary:
the expansion coefficients are irrational, and no irrationality conclusion
about the original sum is asserted.
-/

namespace TailPowerExpansion

open Erdos68Development

noncomputable def columnTail (r N : ℕ) : ℝ :=
  ∑' k : ℕ, powerTerm r (k + N)

noncomputable def scaledColumnTail (r N : ℕ) : ℝ :=
  ((N + 1).factorial : ℝ) ^ (r + 1) * columnTail r N

noncomputable def rowError (J n : ℕ) : ℝ :=
  1 / (((n + 2).factorial : ℝ) ^ J * ((n + 2).factorial - 1 : ℝ))

noncomputable def tailError (J N : ℕ) : ℝ :=
  ∑' k : ℕ, rowError J (k + N)

lemma columnTail_eq (r N : ℕ) :
    columnTail r N = (∑' k : ℕ, powerTerm r k) -
      ∑ k ∈ Finset.range N, powerTerm r k := by
  have h := (summable_powerTerm r).sum_add_tsum_nat_add N
  dsimp [columnTail]
  linarith

lemma irrational_columnTail (r N : ℕ) : Irrational (columnTail r N) := by
  let q : ℚ := ∑ k ∈ Finset.range N, 1 / (((k + 2).factorial : ℚ) ^ (r + 1))
  have hq : (q : ℝ) = ∑ k ∈ Finset.range N, powerTerm r k := by
    simp only [q, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_natCast, powerTerm]
  rw [columnTail_eq, ← hq]
  exact (irrational_sum_powerTerm r).sub_ratCast q

lemma irrational_scaledColumnTail (r N : ℕ) :
    Irrational (scaledColumnTail r N) := by
  have h := (irrational_columnTail r N).natCast_mul
    (show (N + 1).factorial ^ (r + 1) ≠ 0 by positivity)
  simpa only [Nat.cast_pow, scaledColumnTail] using h

lemma columnTail_succ (r N : ℕ) :
    columnTail r N = powerTerm r N + columnTail r (N + 1) := by
  have hs : Summable (fun k => powerTerm r (k + N)) :=
    (summable_nat_add_iff N).mpr (summable_powerTerm r)
  have h := hs.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, zero_add, Nat.add_right_comm  _ 1 N,
    columnTail] using h.symm

lemma scaledColumnTail_succ (r N : ℕ) :
    scaledColumnTail r N =
      (1 + scaledColumnTail r (N + 1)) / (N + 2 : ℝ) ^ (r + 1) := by
  have hf : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (N + 2 : ℝ) ≠ 0 := by positivity
  have hfac : ((N + 2).factorial : ℝ) =
      (N + 2 : ℝ) * ((N + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (N + 1)
  unfold scaledColumnTail
  rw [columnTail_succ]
  simp only [powerTerm, show N + 1 + 1 = N + 2 by omega, hfac, mul_pow]
  field_simp

lemma rowError_pos (J n : ℕ) : 0 < rowError J n := by
  exact one_div_pos.mpr (mul_pos (by positivity) (denom_pos n))

lemma rowError_eq (J n : ℕ) :
    rowError J n = term n / ((n + 2).factorial : ℝ) ^ J := by
  simp [rowError, term, div_eq_mul_inv, mul_comm]

lemma rowError_le_term (J n : ℕ) : rowError J n ≤ term n := by
  rw [rowError_eq]
  apply div_le_self (term_pos n).le
  exact one_le_pow₀ (by linarith [factorial_ge_two n])

lemma summable_rowError (J : ℕ) : Summable (rowError J) :=
  summable_term.of_nonneg_of_le (fun n => (rowError_pos J n).le) (rowError_le_term J)

lemma rowError_split (J n : ℕ) :
    rowError J n = powerTerm J n + rowError (J + 1) n := by
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hd := (denom_pos n).ne'
  unfold rowError powerTerm
  rw [pow_succ]
  field_simp
  ring

lemma tailError_split (J N : ℕ) :
    tailError J N = columnTail J N + tailError (J + 1) N := by
  have h1 : Summable (fun k => powerTerm J (k + N)) :=
    (summable_nat_add_iff N).mpr (summable_powerTerm J)
  have h2 : Summable (fun k => rowError (J + 1) (k + N)) :=
    (summable_nat_add_iff N).mpr (summable_rowError (J + 1))
  simp only [tailError, columnTail, rowError_split J]
  exact h1.tsum_add h2

/-- The remainder after J factorial-power columns is exactly tailError J N. -/
theorem finite_tail_expansion (J N : ℕ) :
    (∑' k : ℕ, term (k + N)) =
      (∑ r ∈ Finset.range J, columnTail r N) + tailError J N := by
  induction J with
  | zero => simp [tailError, rowError, term]
  | succ J ih =>
    rw [ih, Finset.sum_range_succ, tailError_split J]
    ring

lemma tailError_pos (J N : ℕ) : 0 < tailError J N := by
  have hs : Summable (fun k => rowError J (k + N)) :=
    (summable_nat_add_iff N).mpr (summable_rowError J)
  exact hs.tsum_pos (fun k => (rowError_pos J (k + N)).le) 0 (rowError_pos J (0 + N))

lemma tailError_succ (J N : ℕ) :
    tailError J N = rowError J N + tailError J (N + 1) := by
  have hs : Summable (fun k => rowError J (k + N)) :=
    (summable_nat_add_iff N).mpr (summable_rowError J)
  have h := hs.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, zero_add, Nat.add_right_comm _ 1 N,
    tailError] using h.symm

lemma rowError_lt_tailError (J N : ℕ) : rowError J N < tailError J N := by
  rw [tailError_succ]
  linarith [tailError_pos J (N + 1)]

lemma rowError_succ_le (J n : ℕ) :
    rowError J (n + 1) ≤ (1 / (n + 3 : ℝ)) * rowError J n := by
  calc
    rowError J (n + 1) ≤
        ((1 / (n + 3 : ℝ)) * term n) / ((n + 2).factorial : ℝ) ^ J := by
      rw [rowError_eq]
      apply div_le_div₀ (mul_nonneg (by positivity) (term_pos n).le)
        (term_succ_lt n).le (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.factorial_le (show n + 2 ≤ n + 1 + 2 by omega)
    _ = (1 / (n + 3 : ℝ)) * rowError J n := by rw [rowError_eq]; ring

lemma rowError_add_le (J N k : ℕ) :
    rowError J (N + k) ≤ rowError J N * (1 / (N + 3 : ℝ)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      rowError J (N + (k + 1)) ≤
          (1 / (N + k + 3 : ℝ)) * rowError J (N + k) := by
        simpa only [Nat.add_assoc, Nat.cast_add] using rowError_succ_le J (N + k)
      _ ≤ (1 / (N + 3 : ℝ)) *
          (rowError J N * (1 / (N + 3 : ℝ)) ^ k) := by
        apply mul_le_mul ?_ ih (rowError_pos J (N + k)).le (by positivity)
        apply one_div_le_one_div_of_le (by positivity)
        have hk : (0 : ℝ) ≤ k := by positivity
        linarith
      _ = rowError J N * (1 / (N + 3 : ℝ)) ^ (k + 1) := by ring

/-- Explicit positive error bounds for every finite-order tail expansion. -/
theorem tailError_bounds (J N : ℕ) :
    rowError J N < tailError J N ∧
      tailError J N ≤ (N + 3 : ℝ) / (N + 2 : ℝ) * rowError J N := by
  refine ⟨rowError_lt_tailError J N, ?_⟩
  have hp : 0 ≤ (1 / (N + 3 : ℝ)) := by positivity
  have hlt : (1 / (N + 3 : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    have hN : (0 : ℝ) ≤ N := by positivity
    linarith
  have hs : Summable (fun k => rowError J (k + N)) :=
    (summable_nat_add_iff N).mpr (summable_rowError J)
  have hg : Summable (fun k : ℕ => rowError J N * (1 / (N + 3 : ℝ)) ^ k) :=
    (summable_geometric_of_lt_one hp hlt).mul_left _
  calc
    tailError J N ≤ ∑' k : ℕ, rowError J N * (1 / (N + 3 : ℝ)) ^ k := by
      apply hs.tsum_le_tsum _ hg
      intro k
      simpa only [Nat.add_comm k N] using rowError_add_le J N k
    _ = (N + 3 : ℝ) / (N + 2 : ℝ) * rowError J N := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hp hlt]
      have he : (1 : ℝ) - 1 / (N + 3 : ℝ) =
          (N + 2 : ℝ) / (N + 3 : ℝ) := by
        field_simp
        ring
      rw [he, inv_div]
      ring

#print axioms irrational_scaledColumnTail
#print axioms finite_tail_expansion
#print axioms tailError_bounds

end TailPowerExpansion
