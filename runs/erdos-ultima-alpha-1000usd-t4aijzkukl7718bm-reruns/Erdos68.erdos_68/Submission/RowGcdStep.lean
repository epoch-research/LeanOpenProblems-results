import Submission.RowGcdEquality

/-!
An exact integer test for changes of the GCD-corrected approximants.
The required infinite nonvanishing assertion is not proved here.
This file does not settle Erdős 68.
-/

namespace RowGcdStep

open Erdos68Development RowGcdCriterion RowGcdEquality Filter

/-- The numerator of the difference of two successive corrected approximants. -/
def defect (n : ℕ) : ℤ :=
  rowCoeff (n + 1) + rowGcd (n + 1) - (n + 1 : ℤ) * rowGcd n

lemma corrected_step (n : ℕ) :
    gcdCorrected (n + 1) - gcdCorrected n =
      (defect n : ℚ) / (n + 1).factorial := by
  simp only [gcdCorrected, defect, rowCoeff, Int.cast_sub, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, Int.cast_one, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma defect_eq_zero_iff (n : ℕ) :
    defect n = 0 ↔ gcdCorrected (n + 1) = gcdCorrected n := by
  have hf : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  rw [← sub_eq_zero (a := gcdCorrected (n + 1)) (b := gcdCorrected n),
    corrected_step, div_eq_zero_iff]
  simp only [hf, or_false, Int.cast_eq_zero]

lemma eventually_zero_iff :
    (∀ᶠ n : ℕ in atTop, defect n = 0) ↔
      ∃ q : ℚ, ∀ᶠ n : ℕ in atTop, gcdCorrected n = q := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine ⟨gcdCorrected N, eventually_atTop.mpr ⟨N, ?_⟩⟩
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [(defect_eq_zero_iff n).mp (hN n hn), ih]
  · rintro ⟨q, hq⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hq
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    apply (defect_eq_zero_iff n).mpr
    rw [hN n hn, hN (n + 1) (by omega)]

/-- This is an exact reformulation, not a proof of its arithmetic right side. -/
theorem irrational_iff_frequently_nonzero :
    Irrational (∑' k : ℕ, term k) ↔
      ∀ N : ℕ, ∃ n ≥ N, defect n ≠ 0 := by
  rw [irrational_iff_gcdCorrected_not_eventually_constant, ← eventually_zero_iff,
    eventually_atTop]
  push_neg
  rfl

#print axioms corrected_step
#print axioms irrational_iff_frequently_nonzero

end RowGcdStep
