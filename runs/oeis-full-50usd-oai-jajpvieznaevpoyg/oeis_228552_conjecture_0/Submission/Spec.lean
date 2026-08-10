import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
A228552: Square root of the absolute value of A069191(n).
A069191(n) is the determinant of the $n \times n$ matrix $M$ where $M_{i,j} = 1$ if $i+j$ is prime, and $0$ otherwise, for $1 \le i, j \le n$.
$$a(n) = \sqrt{\left|\det\left( \left( \indicator_{\mathbb{P}}(i+j) \right)_{1 \le i, j \le n} \right)\right|}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Matrix.det (Matrix.of (fun (i j : Fin n) =>
    if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))).natAbs.sqrt

/-- oeis_228552_conjecture_0: We conjecture that a(n) > 0 for all n > 15. -/
theorem oeis_228552_conjecture_0 : ∀ n : ℕ, 15 < n → a n > 0 :=
  by sorry
