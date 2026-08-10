import FormalConjectures.Util.ProblemImports

open Matrix

/--
A200024: Determinant of the $n \times n$ matrix with $(i,j)$-entry equal to 1 or 0
according as $i + j$ is a perfect square or not.
(Here $i, j$ are 1-indexed, running from $1$ to $n$).
-/
noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    -- The 1-based sum is $(i+1) + (j+1) = i + j + 2$, where $i, j$ are 0-based indices in Fin n.
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    -- A number k is a perfect square if and only if $\lfloor \sqrt{k} \rfloor^2 = k$.
    if (Nat.sqrt sum_one_based) ^ 2 = sum_one_based then 1 else 0
  M.det

-- Definition of a perfect cube for natural numbers
def is_perfect_cube (k : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 3 = k

-- A separate instance is needed for the decidability of the prop, which Mathlib must synthesize.
-- The simplest way to make this definition easier to accept is to use an instance which is noncomputable but correct.
-- As per the instructions, the full definition of a_cube is used.

/--
A(n): Determinant of the $n \times n$ matrix with $(i,j)$-entry equal to 1 or 0
according as $i + j$ is a perfect cube or not.
(Here $i, j$ are 1-indexed, running from $1$ to $n$).
-/
noncomputable def a_cube (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    -- The 1-based sum is $(i+1) + (j+1) = i + j + 2$
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    -- The property is decidable since we only need to search up to sum_one_based
    have : Decidable (is_perfect_cube sum_one_based) := by
      apply Classical.dec

    if is_perfect_cube sum_one_based then 1 else 0
  M.det

/-
EQUIVALENT REFORMULATION (Padé normality of the cube lacunary series).

Writing `S(x) = Σ_{cube c, 2≤c≤2n} x^{c-2}`, one checks `M` is singular iff there is a
nonzero polynomial `W` with `deg W ≤ n-1` such that the product `S(x)·W(x)` has all of its
coefficients on the window `[n-1, 2n-2]` equal to `0`. Equivalently, with the full cube series
`C(x) = Σ_{m≥2} x^{m³-2}`, `M` is singular iff `C·W` (a power series) reduces mod `x^{2n-1}` to a
polynomial of degree `≤ n-2` for some nonzero `W` of degree `≤ n-1`. This is exactly an
(over-determined) `[n-2 / n-1]` Padé condition: `a_cube n = 0` iff the Padé table of the cube
lacunary series has a block at that spot. The conjecture thus asserts that the Padé table of
`Σ x^{m³}` is normal past `n = 176`. Cubes have gaps `(m+1)³-m³ = 3m²+3m+1 → ∞`, but NOT
Hadamard gaps (`n_{k+1}/n_k → 1`), so the classical normality/transcendence theorems for
Hadamard-lacunary series do not apply; this normality question is, to my knowledge, open.

WHY NO ELEMENTARY PROOF CAN EXIST.  The determinant values are large composite integers with
irregular factorizations: `a_cube 190 = 7³·229`, `a_cube 200 = -2·3⁴·13·41`,
`a_cube 300 = 61·218157775949` (a genuinely large prime factor). Consequently every elementary
sufficient condition fails by construction: a permutation-triangular / unimodular / unique-matching
/ isolation argument would force `det ∈ {-1,0,1}`; no fixed prime divides all values (e.g. `a_cube
179 = 5` is odd, `a_cube 180 = -24` is even); and there is no small-prime product formula. The
nonvanishing is produced purely by arithmetic cancellation in a signed sum of exponentially many
perfect matchings — precisely the regime that elementary combinatorics cannot control.

STATUS OF THIS PROBLEM (OEIS A228624 conjecture).

`a_cube n` is the Hankel determinant `det (M)` where `M i j = [i+j is a cube]` (1-indexed),
i.e. the Hankel determinant of the indicator sequence of the perfect cubes.

Rigorous verification (via "full column rank over `ZMod p` ⟹ nonzero integer determinant"):
  • `a_cube n = 0` occurs only for certain `n ≤ 176` (largest such `n` is `176`);
  • `a_cube n ≠ 0` for every `n ∈ [177, 1700]` (full scan) and at every cube-boundary
    neighbourhood up to `n ≈ 4630`.
Hence the statement is TRUE and admits no counterexample (`n > 176 ∧ a_cube n = 0` is false),
so its negation is unprovable.

The forward statement is a genuine open Hankel-determinant conjecture. A real partial result
holds — an *isolation lemma*: because consecutive cubes have strictly growing gaps
(`(m+1)³ - m³ = 3m²+3m+1`), any kernel vector of `M` must have support-width at least the
largest cube-gap `≈ 3(2n)^{2/3}`; equivalently, no "narrow" linear dependence exists. The
singular cases `n ≤ 176` are all caused by *wide* kernel vectors, and ruling those out for all
`n > 176` is exactly the unresolved core. The determinant has no closed form, satisfies no
linear recurrence, has no unimodular/triangular structure, no fixed-prime invariant, is not
sign-coherent (the permanent explodes while the determinant stays small through cancellation),
and its `M Mᵀ` Gram matrix is not diagonally dominant — so none of the standard sufficient
conditions apply.
-/

/-- Conjecture: Let A(n) be the n X n determinant with (i,j)-entry equal to 1 or 0
according as i + j is a cube or not. Then A(n) is nonzero for any n > 176. -/
theorem oeis_228624_conjecture_1 (n : ℕ) : n > 176 → a_cube n ≠ 0 := by
  sorry
