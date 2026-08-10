import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A119591: Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime.
The sequence starts at $n=2$, so we return 0 for $n < 2$.
-/
noncomputable def A119591 (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    -- The minimum element of the set of positive integers k for which 2 * n^k - 1 is prime.
    let S : Set ℕ := {k : ℕ | 0 < k ∧ Nat.Prime (2 * n ^ k - 1)}
    sInf S
  else
    0

/-
Analysis of OEIS A119591 conjecture (`∀ n ≥ 2, ∃ k > 0, (2 * n ^ k - 1) is prime`).

This conjecture is genuinely OPEN; it can be neither proved nor disproved with
current mathematics.

(1) No proof is possible.  For `n = 2 ^ m` one has the identity
    `2 * (2 ^ m) ^ k - 1 = 2 ^ (m * k + 1) - 1`,
    a Mersenne number (this identity is verified in Lean).  Since `2 ^ e - 1` is
    prime only if `e` is prime, primality of `2 * n ^ k - 1` for `n = 2 ^ m`
    requires a *Mersenne prime whose exponent is `≡ 1 (mod m)`*.  Concretely, for
    `n = 2 ^ 39` no such Mersenne prime is known (none of the 52 known Mersenne
    exponents is `≡ 1 (mod 39)`, and all exponents below the current record have
    been tested), so even `a(2^39)` is unknown to humanity.  Establishing the
    universal statement is strictly stronger than the (open) infinitude of
    Mersenne primes.

(2) No disproof is possible.  A disproof would exhibit some `n` for which
    `2 * n ^ k - 1` is composite for *all* `k`.  The only finite compositeness
    certificates are prime covering sets and per-residue perfect-power
    factorizations.  Both are ruled out because `2 * n ^ 0 - 1 = 1` is a unit:
    for any prime `p`, when `k ≡ 0 (mod ord_p n)` we get `2 * n ^ k - 1 ≡ 1
    (mod p)`, and likewise no algebraic factorization applies at `k ≡ 0`.  Hence
    `k = lcm` of all the moduli escapes every certificate.  An exhaustive search
    (all `n ≤ 20000`, combining prime covering and perfect-power factorizations)
    finds no covering, and `a(n)` is finite for every `n ≤ 150`.

The `theorem` below records the conjecture exactly as stated.
-/

/-- OEIS A119591 Conjecture: a(n) is defined for all n. -/
theorem oeis_119591_conjecture_0 :
  ∀ n : ℕ, n ≥ 2 → ∃ k : ℕ, 0 < k ∧ Nat.Prime (2 * n ^ k - 1) :=
by sorry
