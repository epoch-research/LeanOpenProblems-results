import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
The $n \times n$ Catbert matrix $A_n$ with entries $A_n[i,j] = 1/C(i+j-2)$ for $1 \le i,j \le n$,
where $C(k)$ is the $k$-th Catalan number (A000108).
-/
noncomputable def catbert_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

/--
A296056: Determinant of the inverse of the matrix $A_n$, where $A_n$ is the $n \times n$ matrix
defined by $A_n[i,j] = 1/C(i+j-2)$ for $1 \le i,j \le n$.
$$a(n) = \det(A_n^{-1}) = 1/\det(A_n)$$
-/
noncomputable def A296056 (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (catbert_matrix n).det⁻¹

/--
It is conjectured that a(n) is an integer for all n.
-/
theorem oeis_296056_conjecture_0 (n : ℕ) : A296056 n ∈ Set.range (Int.cast : ℤ → ℚ) :=
  by sorry
