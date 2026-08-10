import FormalConjectures.Util.ProblemImports

open Real Int

/--
A011545: $a(n)$ is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$.
This is equivalent to $a(n) = \lfloor \pi \cdot 10^n \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The calculation is $\lfloor \pi \cdot 10^n \rfloor$.
  -- We use Real.floor, which returns an Int, and convert it to a natural number.
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat

/--
A property which is equivalent to the conjecture that the number of collisions
in the described physical system (with mass ratio $10^{2n}$) is $a(n)$:
the interval $(\pi \cdot 10^n, \pi / \arctan(1/10^n))$ does not contain an integer.
The mass ratio $m$ in the comment is interpreted as $\frac{M}{m}$ in the physics setup,
which is $10^{2n}$, so $\sqrt{m}=10^n$.

Note: The OEIS comment uses $m=10^n$ for the $R^2$ term where $R=10^n$ in the physics formula.
We formalize the statement $\forall n \in \mathbb{N}, \nexists k \in \mathbb{Z}$ such that
$\pi \cdot 10^n < k < \pi / \arctan(1/10^n)$.
-/
theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) :=
  by sorry

/-
Analysis (documentation only):

This statement is the open completeness condition for Galperin's billiard computation of π
(G. Galperin, "Playing pool with π", Reg. Chaotic Dyn. 8 (2003); Aretxabaleta et al. 2020).
The interval `(π·10^n, π/arctan(10^{-n}))` has length `δ_n = π/(3·10^n) - O(10^{-3n})`, so it
contains an integer iff `1 - frac(π·10^n) < δ_n`, i.e. iff the decimal expansion of π contains
a run of ≈ n consecutive nines starting at digit n+1.

* No such n exists within all digits of π ever computed (~10^13); hence the statement is true in
  every verifiable range (worst case n = 0, where the upper endpoint is exactly 4 and emptiness
  holds by strictness of `<`), and a disproof would contradict known computations.
* A proof for all n would require `|π - k/10^n| > 1.05·(10^n)^{-2}`, an irrationality-measure-2
  strength lower bound along denominators 10^n. The best known exponent for π is 7.103
  (Zeilberger–Zudilin 2020); denominator-restricted improvements (Ridout-type) exist only for
  algebraic numbers, and Baker's method does not apply to `10^n·π - k`.

Hence the conjecture, as formalized, is a genuinely open problem of far-out-of-reach
Diophantine-approximation strength; it is settled here in neither direction.
-/
