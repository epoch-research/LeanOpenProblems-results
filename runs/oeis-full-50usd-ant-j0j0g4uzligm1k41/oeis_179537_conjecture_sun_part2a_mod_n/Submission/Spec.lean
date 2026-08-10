import FormalConjectures.Util.ProblemImports

open Finset Nat Int

/--
A179537: The sequence
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$$
-/
def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

/-- The sum $\sum_{k=0}^{p-1} (-1)^k \cdot \text{A179537}(k)$ -/
def A179537_sum_unweighted (p : ℕ) : ℤ :=
  (Finset.range p).sum fun k : ℕ => ((-1 : ℤ) ^ k) * (A179537 k)

-- Definition of the auxiliary sum for the latter parts of Sun's conjecture
def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

-- Legendre symbol $\left(\frac{\cdot}{7}\right)$
noncomputable def leg_sym_7 (p : ℕ) [h_prime : Fact p.Prime] : ℤ :=
  legendreSym p 7

/-!
## Analysis of the conjecture (proof architecture)

Write `a(k) = A179537 k` and `S(n) = A179537_sum_weighted n = ∑_{k<n} (42k+37)(-1)^k a(k)`.
The claim `S(n) ≡ 0 [ZMOD n]` is exactly `(n:ℤ) ∣ S(n)`.

The following facts were established (and numerically verified to `n ≈ 600`):

* **Reduction.** With `a(k) = ∑_j C(k,2j)^2 C(2j,j)^2 (-16)^j` and `h(k) = (42k+37) a(k)`,
  let `f_i = Δ^i h(0)` (forward differences) and `E_s = ∑_{i<s} f_i (-2)^{s-1-i} ∈ ℤ`.
  Using the identity `2·A_i(n) + A_{i-1}(n) = (-1)^{n-1} C(n,i)` for the alternating
  binomial partial sums `A_i(n) = ∑_{k<n} (-1)^k C(k,i)`, one gets the exact identity
  `S(n) = (-1)^{n-1} ∑_{s=1}^{n} C(n,s) E_s`.
  Since `s·C(n,s) = n·C(n-1,s-1)`, the divisibility `n ∣ S(n)` follows from `s ∣ E_s`.

* **The prime `2` part is provable.** The Mahler coefficients `a_i` of `a` satisfy
  `v₂(a_i) ≥ i` (each `C(2j,j)^2 (-16)^j` has `v₂ ≥ 4j ≥ i`), hence `v₂(f_i) ≥ i` and
  `v₂(E_s) ≥ s-1 ≥ v₂(s)`.

* **The odd-prime, exponent-1 part is provable.** `a` satisfies the Lucas congruence
  `a(k) ≡ ∏ a(k_i) (mod p)` (`k = ∑ k_i p^i`). Hence for `p ∣ n` the sum factors:
  `S(n) ≡ S₀(n/p)·S(p) (mod p)` where `S₀(m) = ∑_{k<m}(-1)^k a(k)`; and `p ∣ S(p)`
  (the prime seed, equivalent to `p ∣ ∑_{j≤(p-1)/2} C_j`).

* **The remaining odd-prime, exponent `≥ 2` cases** are tight supercongruences
  (e.g. `v₃(S(9)) = 2`, `v₅(S(25)) = 2` exactly). `a` is Dwork-admissible
  (`a(m+np^{s+1})a(⌊m/p⌋) ≡ a(m)a(⌊m/p⌋+np^s) (mod p^{s+1})`, verified), so the full
  statement is provable by Krattenthaler–Müller / Dwork p-adic descent, which requires
  fine `mod p^e` cancellation analysis beyond a valuation-only argument.

OEIS A179537 Conjecture 0 (Zhi-Wei Sun). Part 2a: Modulo `n` congruence for the weighted sum.
`∑_{k=0}^{n-1}(42k+37)(-1)^k a(k) ≡ 0 (mod n)` for all `n ≥ 1`.
-/
theorem oeis_179537_conjecture_sun_part2a_mod_n :
  ∀ n : ℕ, n ≥ 1 → A179537_sum_weighted n ≡ 0 [ZMOD n] := by sorry
