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

/-- **The key Diophantine lemma.** The whole conjecture reduces exactly to this
inequality: the upper endpoint `π / arctan(10⁻ⁿ)` does not exceed `⌊π·10ⁿ⌋ + 1`.

Mathematically this is equivalent to `⌊π / arctan(10⁻ⁿ)⌋ = ⌊π·10ⁿ⌋`, i.e. Galperin's
"colliding blocks compute the digits of π" statement.  Since
`π/arctan(10⁻ⁿ) - π·10ⁿ = (π/3)·10⁻ⁿ + O(10⁻³ⁿ)`, a failure would force
`|π - m/10ⁿ| < (π/3)·10⁻²ⁿ` for the integer `m = ⌊π·10ⁿ⌋+1`, i.e. an approximation
of quality `c/q²` with `c = π/3 ≈ 1.047` and `q = 10ⁿ`.  As `c > 1/2`, Legendre's
theorem cannot force `m/10ⁿ` to be a continued-fraction convergent of `π`, and the
known irrationality measure of `π` (`μ(π) ≤ 7.11`) is far too weak.  Establishing this
lemma is an OPEN problem (it would follow from `π` having base-10 approximation
exponent `2`, which is unproven and stronger than anything currently known). -/
theorem key_diophantine (n : ℕ) :
    Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)
      ≤ (⌊Real.pi * (10 : ℝ) ^ n.cast⌋ : ℝ) + 1 := by
  sorry

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
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  rintro ⟨k, hkA, hkB⟩
  -- From `π·10ⁿ < k` and `⌊π·10ⁿ⌋ ≤ π·10ⁿ`, the integer `k` exceeds `⌊π·10ⁿ⌋`.
  have h1 : (⌊Real.pi * (10 : ℝ) ^ n.cast⌋ : ℝ) < (k : ℝ) :=
    lt_of_le_of_lt (Int.floor_le _) hkA
  have h2 : ⌊Real.pi * (10 : ℝ) ^ n.cast⌋ < k := by exact_mod_cast h1
  -- Hence `⌊π·10ⁿ⌋ + 1 ≤ k`, so as reals `(⌊π·10ⁿ⌋ : ℝ) + 1 ≤ k`.
  have h3 : ((⌊Real.pi * (10 : ℝ) ^ n.cast⌋ : ℝ) + 1) ≤ (k : ℝ) := by
    have : ⌊Real.pi * (10 : ℝ) ^ n.cast⌋ + 1 ≤ k := h2
    exact_mod_cast this
  -- Combining with the key lemma gives `π/arctan(10⁻ⁿ) ≤ k`, contradicting `k < π/arctan(10⁻ⁿ)`.
  have hbk : Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast) ≤ (k : ℝ) :=
    le_trans (key_diophantine n) h3
  exact absurd hkB (not_lt.mpr hbk)
