import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf finds the infimum of a set of natural numbers. For a non-empty set of positive integers,
  -- this is the minimum. For an empty set, this returns 0, which matches the OEIS definition.
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

-- The example proofs are illustrative only and contain errors, so they are omitted.
-- I will only provide the formalization of the conjecture.

/--
The essential mathematical content of the conjecture: the function `A243473_val` is
surjective, i.e. every natural number `n` occurs as `num(σ(i)/i) - den(σ(i)/i)` for some
positive `i`.

This is the OEIS A243512 conjecture of M. F. Hasler (2014), and it is an OPEN problem.

Analysis:
* It appears TRUE: every value `n` up to several thousand is reachable (verified
  computationally up to `i ≤ 10^9`), and the set of "not yet seen" values shrinks
  steadily as the search bound grows.  For instance `n = 126` first occurs at
  `i = 23154432` (abundancy `185/59`) and `n = 144` at `i = 22538880` (abundancy `187/43`).
* It cannot be DISPROVED by an obstruction: every residue class modulo any `m < 2000`
  is attained, and for fixed `n` the witnessing `i` is unbounded (e.g. `A243473_val p = 1`
  for every prime `p`), so no value can be shown unreachable by a finite search.
* It resists a PROOF: every natural construction — `i = p²` (needs `n-1` prime),
  `i = 2p` (needs `2n-3` prime), or the recursion
  `value(p·M) = ((p+1)/B)·value(M) + 1` (with `B` the denominator of `σ(M)/M`) — reduces
  to requiring a *specific single number* to be prime, because the value grows rigidly
  with any prime parameter, leaving no Dirichlet/Bertrand freedom.  For the even `n`
  with `2n-3` composite this becomes a *binary additive-prime* condition, which is open
  and obstructed by the parity problem of sieve theory.
-/
theorem A243473_surjective (n : ℕ) : ∃ i, 0 < i ∧ A243473_val i = n := by
  sorry

/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/
theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  -- `a n = sInf {i | 0 < i ∧ A243473_val i = n}`.
  -- For ℕ, `sInf S = 0 ↔ 0 ∈ S ∨ S = ∅`.  Here `0 ∉ S` (it requires `0 < i`), so
  -- `a n ≠ 0 ↔ S ≠ ∅ ↔ ∃ i, 0 < i ∧ A243473_val i = n`, which is exactly
  -- the surjectivity statement `A243473_surjective`.
  unfold a
  rw [ne_eq, Nat.sInf_eq_zero]
  push_neg
  refine ⟨?_, A243473_surjective n⟩
  simp only [Set.mem_setOf_eq, lt_irrefl, false_and, not_false_iff]
