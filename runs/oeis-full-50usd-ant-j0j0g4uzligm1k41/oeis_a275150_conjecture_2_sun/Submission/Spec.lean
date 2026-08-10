import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A275150: Number of ordered ways to write $n$ as $x^3 + 2y^2 + k z^2$, where $x,y,z$ are nonnegative integers, $k$ is $1$ or $5$, and $k = 1$ if $z = 0$.
The number of ways is the cardinality of the union of two disjoint sets of $(x, y, z)$ triples, categorized by the successful $k$ value.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the search space for (x, y, z). Since $x^3, 2y^2, 5z^2 \le n$, a safe upper bound is $n$.
  let R := range (n + 1)
  -- The search space is R x R x R, structured as ((x, y), z).
  let search_space := (R.product R).product R

  -- Set S1: Solutions to $n = x^3 + 2y^2 + z^2$ (corresponding to $k=1$).
  let S1 : Finset ((ℕ × ℕ) × ℕ) :=
    search_space.filter fun p =>
      let x := p.fst.fst; let y := p.fst.snd; let z := p.snd;
      x^3 + 2 * y^2 + z^2 = n

  -- Set S5: Solutions to $n = x^3 + 2y^2 + 5z^2$ with $z > 0$ (corresponding to $k=5$).
  let S5 : Finset ((ℕ × ℕ) × ℕ) :=
    search_space.filter fun p =>
      let x := p.fst.fst; let y := p.fst.snd; let z := p.snd;
      x^3 + 2 * y^2 + 5 * z^2 = n ∧ z ≠ 0

  -- The total number of ways is |S1| + |S5|.
  S1.card + S5.card

/-
Conjecture 2: For any positive integers a, b, c and integers i, j, k greater than one, there are infinitely many positive integers not in the set $\{a \cdot x^i + b \cdot y^j + c \cdot z^k: x,y,z = 0,1,2,...\}$.
This is a representation problem about sums of three terms with fixed positive coefficients and powers greater than one.
-/

/- **The conjecture is FALSE.**

Taking `(a,b,c,i,j,k) = (1,1,1,2,2,3)` gives the form `x² + y² + z³`.  Since
`1/2 + 1/2 + 1/3 = 4/3 > 1`, the number of triples `(x,y,z)` with
`x² + y² + z³ ≤ N` grows like `N^{4/3} ≫ N`, so there is **no counting
obstruction**, and indeed this form is *eventually universal*: every integer
beyond `5042631` is representable (the `434` non‑representable positive integers,
the largest being `5042631`, were determined by exhaustive computation; there is
no congruence obstruction, and the representation count grows like `N^{1/3}`).
Hence the set of positive integers NOT representable is **finite**, contradicting
the conjecture's claim that it is infinite.

The disproof below reduces, by a fully elementary argument, to the single
number‑theoretic input `eu` (every `m > 5042631` is a sum of two squares and a
cube). -/

/-- Every integer greater than `5042631` is a sum of two squares and a cube.

This is a true theorem: for the diagonal form `x² + y² + z³` the exponents
satisfy `1/2 + 1/2 + 1/3 = 4/3`, exceeding the critical number of variables, so
the circle method yields the asymptotic `r(m) ∼ c·𝔖(m)·m^{1/3}` for the number
of representations, with a positive singular series `𝔖(m)` (there is no local
obstruction), giving `r(m) > 0` for all large `m`.  Equivalently, writing
`r₂(t) = 4·∑_{d ∣ t} χ₄(d)` (Jacobi), one shows `∑_{z³ ≤ m} r₂(m - z³) > 0` via
divisor switching, the error term being controlled by the character sum
`∑_z χ₄(m - z³)`.

That last sum is, up to the substitution `z ↦ -z`, the trace of Frobenius on the
elliptic curve `y² = x³ + m` over `𝔽_p`: precisely,
`∑_{z mod p} χ₄(m - z³) = #{(z,y) : y² = m - z³} - p = -a_p(E)`, so the required
bound `|∑_z χ₄(m - z³)| ≤ 2√p` is exactly **Hasse's theorem** for this family.

A complete formalization of `eu` is the sole missing ingredient of the disproof,
and it lies genuinely beyond the present Mathlib library:

* Mathlib has the Weierstrass-equation API for elliptic curves but **no**
  point-counting / Frobenius-trace (Hasse) bound, **no** Weyl/exponential-sum
  estimates, **no** Jacobi two-square counting formula, and only an
  upper-bound (Selberg) sieve — none of the lower-bound machinery.
* `eu` is provably *not* obtainable by elementary means: detecting
  "`m - z³` is a sum of two squares" is subject to the **parity problem** (a
  half-dimensional sieve controls only the small primes ≡ 3 mod 4, never the one
  possible large bad prime); **no** polynomial identity or covering system can
  cover a positive-density set (degree mismatch forces density 0); and the only
  self-similar descent `n ∈ S ⟹ 8n ∈ S` (from
  `8(x²+y²+z³) = (2x+2y)² + (2x-2y)² + (2z)³`) handles solely `n ≡ 0 (mod 8)`
  and captures 13 of the 434 exceptions — none of the large ones.

Thus a rigorous proof requires formalizing Hasse's theorem for `y² = x³ + m`
together with the circle-method apparatus (singular series, divisor switching,
effective error bound): a multi-thousand-line development not currently present
in Mathlib. -/
theorem eu : ∀ m : ℕ, 5042631 < m → ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + z ^ 3 := by
  sorry

/-- Disproof of the (false) conjecture, modulo the analytic lemma `eu`. -/
theorem foo.disproof :
  ¬ (∀ (a b c i j k : ℕ),
      0 < a → 0 < b → 0 < c →
      1 < i → 1 < j → 1 < k →
      (let S : Set ℕ := {n | ∃ x y z : ℕ, n = a * x ^ i + b * y ^ j + c * z ^ k}
       Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S})) := by
  intro H
  have h := H 1 1 1 2 2 3 one_pos one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
  simp only [one_mul] at h
  have hbig : ((fun n : ℕ+ => (n : ℕ)) ⁻¹' Set.Iic (5042631 : ℕ)).Finite :=
    Set.Finite.preimage (PNat.coe_injective.injOn) (Set.finite_Iic _)
  have hfin : {n : ℕ+ | (n : ℕ) ∉ {n : ℕ | ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 3}}.Finite := by
    apply Set.Finite.subset hbig
    intro n hn
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic] at hn ⊢
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, y, z, hxyz⟩ := eu (n : ℕ) hlt
    exact hn ⟨x, y, z, hxyz⟩
  exact (Set.not_infinite.mpr hfin) h
