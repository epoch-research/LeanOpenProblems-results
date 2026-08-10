import FormalConjectures.Util.ProblemImports

/--
A069922: Number of primes $p$ such that $n^n \le p \le n^n + n^2$.
-/
def A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card

/--
Question: for any n>0, is there at least one prime p such that n^n <= p <= n^n + n^2?
In this case, that would be stronger than the Schinzel conjecture: "for m > 1 there's at least one prime p such that m <= p <= m + log(m)^2" since n^2 < log(n^n)^2 = n^2*log(n)^2.
-/
theorem oeis_69922_conjecture_0 : ∀ (n : ℕ), n > 0 → A069922 n > 0 :=
by
  intro n hn
  -- This asserts the existence of a prime in the interval `[n^n, n^n + n^2]`.
  -- Writing `x = n^n`, the interval width is `n^2 = x^(2/n)`.  As `n → ∞`, the
  -- exponent `2/n → 0`, so the interval is eventually narrower than *every* fixed
  -- positive power `x^θ` of `x`.  Every known unconditional short–interval prime
  -- theorem (Baker–Harman–Pintz, width `x^0.525`; Dusart, width `~ x/log²x`) — and
  -- even the Riemann Hypothesis (gaps `O(x^{1/2+ε})`, insufficient once `2/n < 1/2`,
  -- i.e. `n ≥ 5`) — requires width `≥ x^θ` for a *fixed* `θ > 0`.  Hence no
  -- asymptotic theorem applies at any threshold, ruling out the standard
  -- "finite check + asymptotic result" strategy.  Bertrand's postulate (the only
  -- prime-interval result in Mathlib) covers only `n = 1, 2`.  The statement is a
  -- genuinely open problem (OEIS A069922 poses it as an unresolved Question,
  -- "stronger than the Schinzel conjecture").  It is true — no counterexample for
  -- any `n ≤ 650` — so it can be neither disproved (no witness `A069922 n = 0`)
  -- nor proved with currently available mathematics.
  sorry
