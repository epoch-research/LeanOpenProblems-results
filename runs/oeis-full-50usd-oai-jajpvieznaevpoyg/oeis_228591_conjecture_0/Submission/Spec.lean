import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
A228591: Determinant of the $n \times n$ $(0,1)$-matrix with $(i,j)$-entry equal to 1 if and only if $i + j$ is 2 or an an odd composite number.
-/
noncomputable def a (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    -- $k$ is the 1-based index sum. The entry is 1 if k=2 or (k is odd and not prime).
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

/--
Conjecture: a(n) = 0 for no n > 15.
-/
theorem oeis_228591_conjecture_0 : ∀ n : ℕ, 15 < n → a n ≠ 0 := by
  sorry

-- We keep the small examples from the prompt for completeness, though they are not required for the final submission.
-- theorem a_one : a 1 = 1 := by trivial
-- theorem a_two : a 2 = 0 := by trivial
-- theorem a_three : a 3 = 0 := by trivial
-- theorem a_four : a 4 = 0 := by trivial
