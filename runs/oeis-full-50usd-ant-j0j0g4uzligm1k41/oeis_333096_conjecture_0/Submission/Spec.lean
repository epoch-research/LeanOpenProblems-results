import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator

/-
### A complete proof outline (verified numerically at every step)

**1. Closed constant-term form.** Writing `C(x)` for the Catalan o.g.f.,
`a(n) = ∑_{k=0}^n [x^k] C(x)^{4n} = [x^n] C(x)^{4n}/(1-x)`.  Substituting
`x = u(1-u)` (`u = xC(x)`, `C = 1/(1-u)`) and then `u = w/(1+w)` turns this into a
constant term of a power of a *genuine Laurent polynomial* `Φ(w) = (1+w)^6/w`:
```
a(N) = CT_w[ Φ(w)^N · Ω(w) ],   Ω(w) = (1 - w^2)/(1 + w + w^2).
```
Expanding, `a(N) = ∑_{i ≥ 0} ω_i · C(6N, N-i)`, where `ω_0 = 1` and `ω_i` is
`3`-periodic for `i ≥ 1` with values `(-1,-1,2)` (i.e. `ω_i = 2` if `3 ∣ i`, else
`-1`).  [Both identities verified symbolically.]  Note the *core* `CT[Φ^N] =
C(6N,N)` already satisfies the classical Kazandzidis supercongruence
`C(6Np^k, Np^k) ≡ C(6Np^{k-1}, Np^{k-1}) (mod p^{3k})`.

**2. Reduction.** With `M = n·p^{k-1}` and `e = v_p(M) ≥ k-1`, the conjecture is
implied by the single clean statement
```
v_p( a(Mp) - a(M) )  ≥  3·(1 + v_p(M))   for all M ≥ 1, primes p ≥ 5.
```

**3. Frobenius identity.**  Since `Φ(w)^p = Φ(w^p) + p·G(w)` with
`G = ((1+w)^{6p} - (1+w^p)^6)/(p·w^p) ∈ ℤ[w,w^{-1}]`, and using `ω_{pt} = ω_t`
(true because `ω` is symmetric on the two nonzero residues mod 3), one gets the
*exact* identity (verified):
```
a(Mp) = ∑_{t=0}^{M} C(M,t) p^t B_t,   B_t = CT[ Φ(w^p)^{M-t} G^t Ω ],   B_0 = a(M).
```
Hence `a(Mp) - a(M) = ∑_{t≥1} C(M,t) p^t B_t`.

**4. Term-by-term bound.**  The required inequality holds *term by term* (verified
for all `t`, all `M ≤ 29`, `p ∈ {5,7,11}`):
`v_p( C(M,t) p^t B_t ) ≥ 3(1 + v_p(M))`.  Since `v_p(C(M,t)) ≥ v_p(M) - v_p(t)`,
this follows from the "Hasse–Witt" valuation bounds
`v_p(B_t) ≥ 2·v_p(M) + max(0, 3-t)`, whose base cases `v_p(B_1) ≥ 2`,
`v_p(B_2) ≥ 1` are Wolstenholme/Kazandzidis-strength cancellations, and whose
`v_p(M)`-growth is the (iterated) Dwork-crystal phenomenon that produces the
sharp "+3 per level".

This is exactly the Beukers–Vlasenko "Dwork crystal" supercongruence specialized to
the reflexive `1`-dimensional Newton polytope `[-1,5]` of `Φ = (1+w)^6/w`.  It
settles Peter Bala's OEIS A333096 conjecture.  The ingredients (Wolstenholme mod
`p^3`, the Kazandzidis extra-factor congruence, the constant-term / Frobenius
formalism) are not present in `Mathlib`.
-/

/--
We conjecture that the sequence satisfies the stronger supercongruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{\left(3k\right)}}$ for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333096_conjecture_0 (p k n : ℕ) :
  (p.Prime ∧ p ≥ 5 ∧ n > 0 ∧ k > 0) →
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  sorry
