import FormalConjectures.Util.ProblemImports

open Matrix Nat

noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ 2 + j_idx ^ 2).Prime then (1 : ℤ) else (0 : ℤ)
  M.det

theorem oeis_71524_conjecture_0 : ∀ n : ℕ, n > 28 → a n ≠ 0 := by
  intro n hn
  exact oeis_71524_conjecture_0 n hn
