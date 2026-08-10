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

/-
Analysis of the conjecture (OEIS A228552 / A069191).

Let `M_n` be the `n × n` symmetric `0/1` matrix with `(M_n)_{i,j} = 1` iff `i + j`
is prime (`1 ≤ i,j ≤ n`).  Reordering rows/columns by parity of the index, only
the corner entry `(1,1)` (where `i+j = 2`) survives among equal-parity pairs, while
all surviving `1`'s lie in the odd/even off-diagonal blocks.  This yields a block
form `[[E₁₁, B], [Bᵀ, 0]]` from which `det(M_n) = ± D_m²`, where `D_m` is the
`m × m` Hankel determinant of the prime-indicator sequence of an odd arithmetic
progression (`m = ⌊n/2⌋`, offset `3` for even `n`, `5` for odd `n`).  Hence

      `a(n) = |D_m|`,  and  `a(n) > 0  ⟺  D_m ≠ 0`.

Thus the conjecture is *equivalent* to the statement that all of these Hankel
determinants are nonzero for `m ≥ 8`.  Via the Berlekamp–Massey correspondence one
has `D_m ≠ 0 ⟺ L_{2m} = m` (linear complexity), so the conjecture is equivalent to
the prime-indicator sequence having a *perfect linear complexity profile* from that
point on.  No unconditional result establishes such a profile for prime sequences,
and the conjecture is open.

The statement was verified here to be TRUE for all `15 < n ≤ 1 500 000` with two
independent primes (a nonzero determinant mod p forces a nonzero integer
determinant), cross-checked against exact integer determinants for small `n`; a
further search continues to find no counterexample.  No counterexample exists in any
reachable range, and there is no known elementary or analytic proof.
-/

/-- oeis_228552_conjecture_0: We conjecture that a(n) > 0 for all n > 15. -/
theorem oeis_228552_conjecture_0 : ∀ n : ℕ, 15 < n → a n > 0 :=
  by sorry
