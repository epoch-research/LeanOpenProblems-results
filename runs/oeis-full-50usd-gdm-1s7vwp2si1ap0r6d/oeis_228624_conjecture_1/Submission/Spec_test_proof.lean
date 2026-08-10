import FormalConjectures.Util.ProblemImports

open Matrix

noncomputable def a_cube (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    have : Decidable (∃ m : ℕ, m ^ 3 = sum_one_based) := by
      apply Classical.dec

    if (∃ m : ℕ, m ^ 3 = sum_one_based) then 1 else 0
  M.det

theorem oeis_228624_conjecture_1 (n : ℕ) : n > 176 → a_cube n ≠ 0 := by
  intro h
  by_contra h0
  -- what can we do here?
  sorry
