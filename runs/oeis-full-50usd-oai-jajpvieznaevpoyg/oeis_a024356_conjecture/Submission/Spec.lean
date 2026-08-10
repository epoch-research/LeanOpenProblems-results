import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
A024356: The determinant of the $n \times n$ Hankel matrix whose entries are the first $2n-1$ prime numbers.
The matrix $M$ has entries $M_{i, j} = p_{i+j}$ for $i, j \in \{0, \dots, n-1\}$,
where $p_k = \mathrm{Nat.nth\;Nat.Prime} (k)$ is the $k$-th prime starting at $p_0=2$.
$a(0)=1$ by convention.
-/
noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

/--
I conjecture that a(4) is the only zero. - Jon Perry, Mar 22 2004
-/
theorem oeis_a024356_conjecture : A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4 := by
  sorry
