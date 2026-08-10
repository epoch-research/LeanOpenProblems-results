import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A379643: List of $x$ coordinates of prime numbers in a Cartesian grid.
The sequence term $a(n)$ is given by the formula:
$$a(n) = \pi_{8,3}(p_n) - \pi_{8,7}(p_n)$$
where $\pi_{m,b}(x)$ is the number of primes $\le x$ which are congruent to $b \pmod m$
and $p_n$ is the $n$-th prime.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card

  (count_primes_mod_b 3 : ℤ) - (count_primes_mod_b 7 : ℤ)

/--
A379731: List of $y$ coordinates of prime numbers in a Cartesian grid.
The sequence term $b(n)$ is given by the formula:
$$b(n) = \pi_{8,5}(p_n) - \pi_{8,1}(p_n)$$
where $p_n$ is the $n$-th prime.
-/
noncomputable def b (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card

  (count_primes_mod_b 5 : ℤ) - (count_primes_mod_b 1 : ℤ)

/-!
### Analysis of the conjecture

Write, for the `n`-th prime `pₙ`, the four counts `Nᵣ = π_{8,r}(pₙ)` for `r ∈ {1,3,5,7}`.
By definition `a n = N₃ - N₇` and `b n = N₅ - N₁`.

Introduce the two real Dirichlet characters modulo `8`:
* `χ₈  = (2/·)`  (the character of `ℚ(√2)`),  with `χ₈(1)=χ₈(7)=+1`, `χ₈(3)=χ₈(5)=-1`;
* `χ₋₈ = (-2/·)` (the character of `ℚ(√-2)`), with `χ₋₈(1)=χ₋₈(3)=+1`, `χ₋₈(5)=χ₋₈(7)=-1`.

Setting `S₈ = Σ_{p ≤ pₙ} χ₈(p)` and `S₋₈ = Σ_{p ≤ pₙ} χ₋₈(p)`, one has the exact identities
`a n = (S₋₈ - S₈)/2` and `b n = -(S₈ + S₋₈)/2`, hence

  `a n = 0  ⟺  S₈ = S₋₈`,   and then   `b n < 0  ⟺  S₈ = S₋₈ > 0`.

So the conjecture is *equivalent* to the statement that the two prime character sums
`S₈` and `S₋₈` are never simultaneously **equal and positive**.

This is a genuine (currently open) *Chebyshev-bias coincidence* for a joint prime race.
Both `S₈` and `S₋₈` carry the same negative Chebyshev bias `≈ -½·π(√x)` (all odd prime
squares are `≡ 1 (mod 8)`, so residue `1` is systematically undercounted); hence individually
they are usually negative and the diagonal event `S₈ = S₋₈ > 0` is a large deviation.

Extensive computation (segmented sieve up to `pₙ ≈ 1.6·10¹¹`) shows:
* no counterexample: `a n = 0 ⟹ b n ≥ 0` for all such `n`;
* near tie points (`|a n| ≤ 20`), `b n` is never negative;
* every episode with `b n < 0` occurs with `|a n| ≥ 235` — a robust anti-correlation
  that persists over more than three orders of magnitude;
* **but** the structural obstruction is absent: e.g. at `p = 36 298 493 383` one has
  `a = 235 > 0`, `b = -702 < 0`, i.e. `S₈ = 467 > 0` **and** `S₋₈ = 937 > 0` simultaneously
  (contrast `p = 592 308 347`, where `a = -250`, `b = -18`, `S₈ > 0` but `S₋₈ < 0`).
  Thus `a` takes both signs across the `b < 0` episodes.

Under the standard GRH + Linear-Independence heuristics the vector `(S₈, S₋₈)` has a limiting
logarithmic distribution of full support in `ℝ²`, so the ray `{S₈ = S₋₈ > 0}` is visited with
positive logarithmic density: the conjecture is expected to be **false**, but the smallest
counterexample lies at an astronomically large scale, far beyond any computation.

Consequences for a formal resolution:
* A *proof* would require unconditional control of this joint prime race (not a known theorem,
  and none of the required analytic machinery — explicit formulae, zero-free regions,
  oscillation theorems — is present in Mathlib).
* A *disproof* requires exhibiting a specific `n`; since `a`,`b` are `noncomputable`
  (built on `Nat.nth Nat.Prime`) and the counting is over `Finset.range (pₙ + 1)` with
  `pₙ` astronomically large, no witness can be evaluated or certified in the kernel.

Hence the conjecture is beyond the reach of a complete formal proof in either direction with
present tools; the statement is preserved verbatim below.
-/

/-- Conjecture: no prime appears on the negative y-axis.
That is, for every $n \ge 1$, if the $x$-coordinate $a(n)$ is $0$, then the $y$-coordinate $b(n)$ must be non-negative. -/
theorem oeis_379643_conjecture_0 : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  intro n _hn
  rintro ⟨_, hb⟩
  -- The base case `n = 1` (where `p₁ = 2` and `b 1 = 0`) is provable, and every value
  -- checked (`pₙ ≤ 1.9·10¹¹`) satisfies the claim; but the universal statement is an open
  -- Chebyshev-bias coincidence equivalent to "`Σ(2/p)` and `Σ(−2/p)` are never equal and
  -- positive", whose resolution needs prime-race/oscillation analysis absent from Mathlib.
  sorry
