import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
A228591: Determinant of the $n \times n$ $(0,1)$-matrix with $(i,j)$-entry equal to 1 if and only if $i + j$ is 2 or an an odd composite number.
-/
noncomputable def a (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

theorem oeis_228591_conjecture_0 : ∀ n : ℕ, 15 < n → a n ≠ 0 := by
  sorry

theorem oeis_228591_conjecture_0.disproof : ¬ (type_of% @oeis_228591_conjecture_0) := by
  sorry
