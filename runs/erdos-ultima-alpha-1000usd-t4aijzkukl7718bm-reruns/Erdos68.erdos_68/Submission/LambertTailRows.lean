import Submission.LambertDifferenceCheck
import Submission.LambertRawBounds

/-! Exact summation of the geometric Lambert tails and interchange with
finite raw operators. These are auxiliary results, not a settlement. -/
namespace LambertTailRows

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds

noncomputable def row (n k : ℕ) : ℝ := geometricRowTail (k + 2) n

lemma row_nonneg (n k : ℕ) : 0 ≤ row n k := by
  have hd := denom_pos k
  unfold row geometricRowTail
  positivity

lemma row_le_term (n k : ℕ) : row n k ≤ term k := by
  have hf := factorial_ge_two k
  have hd := denom_pos k
  have hp : (1 : ℝ) ≤ ((k + 2).factorial : ℝ) ^ (n / (k + 2)) :=
    one_le_pow₀ (by linarith)
  unfold row geometricRowTail term
  apply one_div_le_one_div_of_le hd
  nlinarith

lemma summable_row (n : ℕ) : Summable (row n) :=
  Summable.of_nonneg_of_le (row_nonneg n) (row_le_term n) summable_term

lemma row_step (d n : ℕ) (hd : 2 ≤ d) :
    geometricRowTail d n - geometricRowTail d (n + 1) =
      if d ∣ n + 1 then 1 / (d.factorial : ℝ) ^ ((n + 1) / d) else 0 := by
  have hf : (2 : ℝ) ≤ d.factorial := by
    exact_mod_cast (show 2 ≤ d.factorial from by simpa using Nat.factorial_le hd)
  have hfn : (d.factorial : ℝ) ≠ 0 := by positivity
  have hfd : (d.factorial : ℝ) - 1 ≠ 0 := by linarith
  by_cases h : d ∣ n + 1
  · simp only [if_pos h, geometricRowTail, Nat.succ_div_of_dvd h, pow_succ]
    field_simp
  · simp [h, geometricRowTail, Nat.succ_div_of_not_dvd h]

noncomputable def atom (m d : ℕ) : ℝ :=
  if 2 ≤ d ∧ d ∣ m then 1 / (d.factorial : ℝ) ^ (m / d) else 0

lemma atom_eq_zero_off_divisors (m : ℕ) (hm : 0 < m) (d : ℕ)
    (hd : d ∉ m.divisors) : atom m d = 0 := by
  have hnd : ¬ d ∣ m := by simpa [Nat.mem_divisors, hm.ne'] using hd
  simp [atom, hnd]

lemma summable_atom (m : ℕ) (hm : 0 < m) : Summable (atom m) :=
  summable_of_ne_finset_zero (s := m.divisors) (atom_eq_zero_off_divisors m hm)

lemma tsum_atom (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ, atom m d) = (lambertCoeff m : ℝ) / m.factorial := by
  rw [tsum_eq_sum (s := m.divisors) (atom_eq_zero_off_divisors m hm), lambertCoeff_cast_div]
  apply Finset.sum_congr rfl
  intro d hd
  simp [atom, Nat.dvd_of_mem_divisors hd]

lemma tsum_atom_add_two (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, atom m (k + 2)) = (lambertCoeff m : ℝ) / m.factorial := by
  have h := (summable_atom m hm).sum_add_tsum_nat_add 2
  rw [tsum_atom m hm] at h
  simpa [Finset.sum_range_succ, atom] using h

lemma tsum_row_step (n : ℕ) :
    (∑' k : ℕ, row n k) - (∑' k : ℕ, row (n + 1) k) =
      (lambertCoeff (n + 1) : ℝ) / (n + 1).factorial := by
  rw [← (summable_row n).tsum_sub (summable_row (n + 1))]
  have he : (fun k => row n k - row (n + 1) k) = fun k => atom (n + 1) (k + 2) := by
    funext k
    simp only [row, row_step (k + 2) n (by omega), atom, show 2 ≤ k + 2 by omega,
      true_and]
  rw [he]
  exact tsum_atom_add_two (n + 1) (by omega)

/-- The exact row decomposition of the unscaled Lambert tail. -/
theorem tsum_row (n : ℕ) :
    (∑' k : ℕ, row n k) = (∑' k : ℕ, term k) - (prefixQ n : ℝ) := by
  induction n with
  | zero => simp [row, geometricRowTail, prefixQ, lambertCoeff, term]
  | succ n ih =>
    have hs := tsum_row_step n
    have hp : (prefixQ (n + 1) : ℝ) = (prefixQ n : ℝ) +
        (lambertCoeff (n + 1) : ℝ) / (n + 1).factorial := by
      simp only [prefixQ, Finset.sum_range_succ, Rat.cast_add, Rat.cast_div,
        Rat.cast_natCast]
    rw [ih] at hs
    rw [hp]
    linarith

lemma summable_rawApply (ds : List ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ n, Summable (f n)) (n : ℕ) :
    Summable (fun k => rawApply ds (fun n => f n k) n) := by
  induction ds generalizing f with
  | nil => exact hf n
  | cons d ds ih =>
    apply ih (fun n k => rawShift d (fun n => f n k) n)
    intro n
    exact ((hf (n + d)).mul_left _).sub (hf n)

lemma rawApply_tsum (ds : List ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ n, Summable (f n)) (n : ℕ) :
    rawApply ds (fun n => ∑' k : ℕ, f n k) n =
      ∑' k : ℕ, rawApply ds (fun n => f n k) n := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
    have hs (n : ℕ) : Summable (fun k => rawShift d (fun n => f n k) n) :=
      ((hf (n + d)).mul_left _).sub (hf n)
    have he : rawShift d (fun n => ∑' k : ℕ, f n k) =
        fun n => ∑' k : ℕ, rawShift d (fun n => f n k) n := by
      funext n
      simp only [rawShift]
      rw [((hf (n + d)).mul_left _).tsum_sub (hf n), tsum_mul_left]
    rw [rawApply, he, ih _ hs]
    rfl

/-- Applying any finite raw operator commutes with the geometric row sum. -/
theorem rawApply_tail_rows (ds : List ℕ) (n : ℕ) :
    rawApply ds (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n =
      ∑' k : ℕ, rawApply ds (geometricRowTail (k + 2)) n := by
  have he : (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) =
      fun n => ∑' k : ℕ, row n k := by
    funext n
    exact (tsum_row n).symm
  rw [he, rawApply_tsum ds row summable_row]
  rfl

end LambertTailRows

#print axioms LambertTailRows.tsum_row
#print axioms LambertTailRows.rawApply_tail_rows
