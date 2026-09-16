import FormalConjectures.Util.ProblemImports

open Matrix

noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    if (Nat.sqrt sum_one_based) ^ 2 = sum_one_based then 1 else 0
  M.det

def is_perfect_cube (k : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 3 = k

noncomputable def a_cube (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    have : Decidable (is_perfect_cube sum_one_based) := by
      apply Classical.dec
    if is_perfect_cube sum_one_based then 1 else 0
  M.det

theorem oeis_228624_conjecture_1 (n : ℕ) : n > 176 → a_cube n ≠ 0 := by
  sorry

theorem oeis_228624_conjecture_1.disproof : ¬ (type_of% @oeis_228624_conjecture_1) := by
  sorry
