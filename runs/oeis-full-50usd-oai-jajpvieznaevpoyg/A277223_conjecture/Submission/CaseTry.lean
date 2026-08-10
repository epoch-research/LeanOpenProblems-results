import FormalConjectures.Util.ProblemImports

open Nat Set
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers

example (n : ℕ) (hn : n > 0) (hlt : A277223 n < 12)
    (hmem : A277223 n = sum_digits_10 (A277223 n * n)) :
    A277223 n = 0 ∨ A277223 n = 9 := by
  have hmod := Nat.modEq_nine_digits_sum (A277223 n * n)
  rw [← hmem] at hmod
  have hA : A277223 n ≤ 11 := by omega
  interval_cases A277223 n <;> simp_all [sum_digits_10] <;> try omega
