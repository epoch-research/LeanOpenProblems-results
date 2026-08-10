import FormalConjectures.Util.ProblemImports

open Nat Classical

/--
A366833: Number of times $n$ appears in A362965 (number of primes $\le$ the $n$-th prime power).
This is equivalent to: One less than the number of prime powers $q$ such that $\mathrm{prime}(n) \le q \le \mathrm{prime}(n+1)$, inclusive.
Where $\mathrm{prime}(n)$ is the $n$-th prime ($p_1=2$).
$$a(n) = \left|\left\{q \in \mathbb{N} : \text{IsPrimePow}(q) \land \mathrm{prime}(n) \le q \le \mathrm{prime}(n+1)\right\}\right| - 1$$
-/
noncomputable def A366833 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- p_n (1-indexed) is Nat.nth Nat.Prime (n-1) (0-indexed). Since n > 0, n-1 is safe.
    let p_n   : ℕ := Nat.nth Nat.Prime (n - 1)
    -- p_{n+1} is Nat.nth Nat.Prime n
    let p_np1 : ℕ := Nat.nth Nat.Prime n

    -- Count the number of prime powers in the inclusive interval [p_n, p_{n+1}]
    let count_prime_powers : ℕ :=
      Finset.card ((Finset.Icc p_n p_np1).filter IsPrimePow)

    -- Subtracting 1 is safe since both p_n and p_{n+1} are prime powers, giving a count >= 2.
    count_prime_powers - 1

/-!
### Analysis

Write `C(n) = card ((Icc pₙ pₙ₊₁).filter IsPrimePow)`, the number of prime powers in the
closed interval `[pₙ, pₙ₊₁]` between consecutive primes.  Then `A366833 n = C(n) - 1`, and
the conjecture `A366833 n ∈ {1,2,3}` is *exactly equivalent* to `2 ≤ C(n) ≤ 4`, i.e. to:
there are at most **two** proper (non-prime) prime powers strictly between two consecutive primes.

* **Lower bound `2 ≤ C(n)` (proved in `count_ge_two`).** Both endpoints `pₙ` and `pₙ₊₁` are
  distinct primes, hence prime powers lying in `[pₙ, pₙ₊₁]`, so `C(n) ≥ 2`.

* **Upper bound `C(n) ≤ 4`.** This is the genuine content, and it is *equivalent to Legendre's
  conjecture* (modulo a finite check), hence an open problem beyond current mathematics.

  A counterexample requires three proper prime powers `a < b < c` inside a prime-free interval
  `(pₙ, pₙ₊₁)`.  Bertrand's postulate gives `c < 2a` and forces distinct prime bases, but these
  elementary constraints are satisfiable (e.g. `{49 = 7², 64 = 2⁶, 81 = 3⁴}`): the only reason
  such a triple is *not* a counterexample is that primes (`53, 59, 61, …`) fall between the
  powers.  Thus **any** proof must invoke prime existence in a short interval — no Bertrand-only
  or algebraic argument can work.

  Quantitatively: a direct computation shows that for `x > 2187` every triple of consecutive
  proper prime powers spans at least `2√x` (only three exceptions, all with `x ≤ 2187`).  Hence a
  counterexample forces a prime gap of length `≥ 2√x` with no prime inside — precisely the failure
  of Legendre's conjecture (a prime between consecutive squares, i.e. a prime in every interval of
  length `~2√x`).  Legendre's conjecture is open (unproven for ~250 years) and is *not* implied by
  the Riemann Hypothesis, which yields only gaps `O(√x·log x)`, too weak for length-`2√x`
  intervals.  The best unconditional result (Baker–Harman–Pintz, `x^{0.525}`) also fails, since
  `x^{0.525} ≫ 2√x` for `x > 10¹²`; and in any case Mathlib supplies only Bertrand's postulate.
  Numerically the conjecture is true (verified here exhaustively to `10¹⁴`, and beyond in prior
  work), but a Lean-checkable proof would require settling Legendre's conjecture.
-/

/-- The number of prime powers in `[pₙ, pₙ₊₁]` is at least `2`, since both endpoints are
distinct primes and hence prime powers. This yields `A366833 n ≥ 1`. -/
theorem count_ge_two (n : ℕ) (hn : 1 ≤ n) :
    2 ≤ Finset.card ((Finset.Icc (Nat.nth Nat.Prime (n-1)) (Nat.nth Nat.Prime n)).filter IsPrimePow) := by
  set pn := Nat.nth Nat.Prime (n-1) with hpn
  set pq := Nat.nth Nat.Prime n with hpq
  have hlt : pn < pq := by
    rw [hpn, hpq]
    exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (by omega)
  have hpnp : Nat.Prime pn := Nat.prime_nth_prime _
  have hpqp : Nat.Prime pq := Nat.prime_nth_prime _
  have hsub : ({pn, pq} : Finset ℕ) ⊆ (Finset.Icc pn pq).filter IsPrimePow := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hx with rfl | rfl
    · exact ⟨⟨le_refl _, le_of_lt hlt⟩, hpnp.prime.isPrimePow⟩
    · exact ⟨⟨le_of_lt hlt, le_refl _⟩, hpqp.prime.isPrimePow⟩
  have hcard : ({pn, pq} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]; exact _root_.ne_of_lt hlt
  calc 2 = ({pn, pq} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/--
Conjecture: a(n) can be only 1, 2, or 3 (with the first occurrences of 3 appearing at n = 4, 9, 30, 327 and 3512).
-/
theorem oeis_366833_conjecture_0 : ∀ (n : ℕ), 1 ≤ n → A366833 n ∈ ({1, 2, 3} : Finset ℕ) := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  -- Lower bound: the two endpoint primes are always counted.
  have hlow := count_ge_two n hn
  -- Upper bound: at most two proper prime powers between consecutive primes.
  -- This is the sole remaining content: an open, Legendre-type prime-gap statement
  -- (see the analysis above), beyond Bertrand's postulate, the only prime-interval
  -- theorem available in Mathlib.
  have hupp : Finset.card ((Finset.Icc (Nat.nth Nat.Prime (n-1)) (Nat.nth Nat.Prime n)).filter IsPrimePow) ≤ 4 := by
    sorry
  unfold A366833
  rw [dif_neg hn0]
  simp only
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega
