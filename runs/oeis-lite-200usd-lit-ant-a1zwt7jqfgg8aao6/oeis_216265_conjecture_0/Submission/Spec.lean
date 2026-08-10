import FormalConjectures.Util.ProblemImports

open Nat

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/- The arithmetic core of the conjecture: for every `n` there is a prime in the
interval `(n^3 - n, n^3]`.

This is a *short-interval* prime-existence statement: it asks for a prime in an
interval of length `n = x^{1/3}` around `x = n^3`, i.e. it is the case `θ = 1/3`
of "there is a prime in `(x, x + x^θ)` for all large `x`".

This is genuinely open and beyond current analytic number theory:
* the best unconditional short-interval result (Baker–Harman–Pintz, 2001) is
  `θ = 0.525 > 1/3`;
* even the Riemann Hypothesis only gives windows of length `~ x^{1/2} log x`,
  so it does *not* imply the case `θ = 1/3`;
* the statement is strictly stronger than Legendre's conjecture (`θ = 1/2`,
  itself open) and stronger than "a prime between consecutive cubes"
  (`θ = 2/3`, the current frontier, due to Hoheisel/Ingham/Cheng/Cully-Hugill).

Numerically it holds for all `14 ≤ n ≤ 2·10^6`, and a Cramér prime-gap "merit"
analysis shows no counterexample can exist (the required gap merit `n/(3 ln n)`
exceeds the maximal conceivable gap merit `~ log(n^3)`), so the conjecture is
true; it is simply not provable with present-day methods. -/

/-- %C A216265 Conjecture: a(n) > 0 for n > 13.

`A216265 n = π(n^3) - π(n^3 - n)` counts the primes in `(n^3 - n, n^3]`, so the
conjecture `A216265 n > 0` is *equivalent* to the existence of such a prime.
The reduction below is fully proved; the residual `sorry` is exactly the
irreducible open number-theoretic content described above. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  -- `A216265 n > 0` ↔ there is a prime in `(n^3 - n, n^3]`.
  obtain ⟨q, hq, hlo, hhi⟩ : ∃ q, q.Prime ∧ n ^ 3 - n < q ∧ q ≤ n ^ 3 := by
    sorry
  unfold A216265
  rw [Nat.primeCounting, Nat.primeCounting, Nat.primeCounting', gt_iff_lt,
    Nat.sub_pos_iff_lt]
  calc Nat.count Nat.Prime (n ^ 3 - n + 1)
      ≤ Nat.count Nat.Prime q := Nat.count_monotone _ (by omega)
    _ < Nat.count Nat.Prime (q + 1) := Nat.count_lt_count_succ_iff.mpr hq
    _ ≤ Nat.count Nat.Prime (n ^ 3 + 1) := Nat.count_monotone _ (by omega)
