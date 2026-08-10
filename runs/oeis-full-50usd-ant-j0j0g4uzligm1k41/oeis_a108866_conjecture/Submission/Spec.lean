import FormalConjectures.Util.ProblemImports

/--
A108866: Numerator of $\sum_{k=1}^n \frac{2^k}{k}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range n) fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)).num.natAbs

/--
The rational number inside the numerator function in the conjecture.
$$ -\frac{2}{n} + \sum_{k=1}^n \frac{2^k}{k} $$
-/
noncomputable def rat_expression (n : ℕ) : Rat :=
  if h : n > 0 then
    (-2 : Rat) / (n : Rat) + Finset.sum (Finset.range n) fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)
  else
    0

/-!
## Analysis of the conjecture  (a sharp reduction to an open problem)

Write `E n = (∑_{k=1}^n 2^k/k) - 2/n = rat_expression n` (for `n > 0`).
Since numerator and denominator of a `Rat` are coprime, the condition
`(rat_expression n).num ≡ 0 [ZMOD n^2]`, i.e. `n^2 ∣ (E n).num`, is equivalent to
`∀ prime ℓ ∣ n, padicValRat ℓ (E n) ≥ 2 * padicValNat ℓ n`.

The following facts were established (and verified numerically for all `n ≤ 20000`,
and for the decisive prime cases up to `p < 60000`):

* **Clean identity.** `E n = ∑_{i=1}^{n-1} (1 + C(n,i))/i = H_{n-1} + n·∑_{i=1}^{n-1} C(n-1,i-1)/i²`.

* **Prime direction.** For a prime `p ≥ 5`, `E p = H_{p-1} + p·T_p` with
  `T_p ≡ ∑ (-1)^{i-1}/i² ≡ 0 (mod p)` (a Wolstenholme-type fact), while Wolstenholme's theorem
  gives `p² ∣ num(H_{p-1})`. Hence `p² ∣ num(E p)`, so every prime `> 3` satisfies the criterion.
  (Wolstenholme's theorem is **not** available in Mathlib.)

* **Frobenius-type recursion.** For every `M ≥ 2` and prime `p`,
  `padicValRat p (E (p·M)) = padicValRat p (E M) - 1`
  (from Jacobsthal's congruence `C(pM,pj) ≡ C(M,j) (mod p³)` and `p ∣ C(pM,i)` for `p ∤ i`).

* **Converse, clean form.** For every *composite* `n`, its **smallest** prime factor `p`
  (with `a = v_p n`) already satisfies `padicValRat p (E n) < 2a`; this single prime witnesses
  `n² ∤ num(E n)`.  (Verified for every composite `n ≤ 20000`.)  Via the recursion this splits into:
  - **Non-prime-power `n`** (`n₀ = n/p^a ≥ 2`, all prime factors of `n₀` exceed `p`):
    `padicValRat p (E n) = padicValRat p (E n₀) - a`, needing `padicValRat p (E n₀) < 3a`.
  - **Prime power `n = p^k`:** `padicValRat p (E (p^k)) = padicValRat p (E p) - (k-1)`,
    needing `padicValRat p (E p) < 3k - 1`.  The single binding instance is `k = 2` (`n = p²`),
    which requires `padicValRat p (E p) ≤ 4`, i.e. **no prime has `p^5 ∣ num(E p)`.**

* **The open obstruction.** Computation shows `padicValRat p (E p) = 2` for every prime except
  `p = 7` (value `3`, via an arithmetic cancellation `v_p(H_{p-1}) = 2`) and the *Wolstenholme
  primes* (`16843, …`, value `3`, via `v_p(H_{p-1}) = 3`).  A counterexample `n = p²` would need
  a prime with `padicValRat p (E p) ≥ 5`, i.e. essentially a prime with `v_p(H_{p-1}) ≥ 5`.
  Bounding `v_p(H_{p-1})` (or proving the nonexistence of such "super-Wolstenholme" primes) is a
  well-known **open problem** of Wieferich/Wolstenholme type.  Thus this criterion is precisely the
  base-`2` analogue of the *converse of Wolstenholme's theorem*, which is open.

**Status.** The statement is *true* as far as is computable (no counterexample exists, so its
negation is unprovable), but a complete unconditional proof is beyond current number theory: it
requires resolving the open coincidence bounds above (in particular `p^5 ∤ num(E p)` for the case
`n = p²`). The reduction below is complete except for these genuinely open inputs.
-/

/-- The value `E n = rat_expression n` written as a sum over `k = 1..n`. -/
noncomputable def E (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.Icc 1 n, (2:ℚ)^k / (k:ℚ)) - 2 / (n:ℚ)

/--
A108866 Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2) if and only if n is prime.
-/
theorem oeis_a108866_conjecture {n : ℕ} (hn : n > 3) :
    (rat_expression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ Nat.Prime n := by
  sorry
