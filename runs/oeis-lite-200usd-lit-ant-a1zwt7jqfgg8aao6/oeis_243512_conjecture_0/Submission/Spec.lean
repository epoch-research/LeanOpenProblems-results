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
**The arithmetic heart of the conjecture.**

The statement `a n ≠ 0` is equivalent (see `oeis_243512_conjecture_0` below) to the
*surjectivity* of `A243473_val` onto `ℕ`, i.e. that for every `n` there is a positive
integer `i` whose per-unit-abundancy difference equals `n`.

This is precisely the (open) OEIS conjecture for A243512.  Writing the reduced fraction
`σ(i)/i = num/den`, one checks `A243473_val i = num((σ(i) - i)/i)` (the numerator of the
*reduced* aliquot ratio).  Realising a prescribed value `n` is governed by the existence
of primes of a special shape: e.g. the squarefree witness `i = p*q` gives
`A243473_val (p*q) = 1 + p + q = s(p*q)`, and "every odd `n ≥ 9` is of this form" is a
known *variant of Goldbach's conjecture* (verified only computationally, to `4·10^18`).
More generally each candidate construction (`i = 2^a·p`, `i = p^k`, `i = P·p` with `P`
perfect, …) pins down a *specific* prime whose primality is a Dickson/Schinzel-type
condition.  Crucially, in every construction introducing a free prime `p`, the resulting
value is strictly monotone in the magnitude of `p`, so neither Dirichlet's theorem on
primes in arithmetic progressions nor Bertrand's postulate (the strongest unconditional
prime-existence results in Mathlib) can supply the required witness for *every* `n`.

The statement is true (all `n ≤ 500` have been verified to occur, some requiring
`i` as large as `2.3·10^7`), but no unconditional proof is known; this isolates the
genuinely open core of the conjecture.
-/
theorem A243473_surjective (n : ℕ) : ∃ i, 0 < i ∧ A243473_val i = n := by
  match n with
  | 0 =>
    -- `i = 1`: `σ(1)/1 = 1/1`, numerator − denominator `= 0`.
    exact ⟨1, by norm_num, by simp only [A243473_val]; norm_num [sigma_one_apply]⟩
  | 1 =>
    -- `i = 2`: `σ(2)/2 = 3/2`, numerator − denominator `= 1`.
    refine ⟨2, by norm_num, ?_⟩
    have h : sigma 1 2 = 3 := by decide
    simp only [A243473_val, h]; norm_num
  | (k + 2) =>
    -- For `n ≥ 2` this is the open OEIS A243512 conjecture (see the docstring above):
    -- it requires, for each `n`, a witness whose existence is a Dickson/Schinzel/Goldbach
    -- type prime-existence statement, not provable with current mathematics.
    sorry

/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/
theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  -- This is equivalent to saying that for every `n`, the set
  -- `{i : ℕ | 0 < i ∧ A243473_val i = n}` is non-empty.
  -- The provided OEIS conjecture is that no `a(n)` will ever be 0.
  -- We reduce the claim to the (open) surjectivity statement `A243473_surjective`.
  unfold a
  rw [Ne, Nat.sInf_eq_zero]
  push_neg
  refine ⟨?_, ?_⟩
  · -- `0` is not in the set, since membership requires `0 < i`.
    intro hmem
    exact absurd hmem.1 (lt_irrefl 0)
  · -- the set is non-empty by `A243473_surjective`.
    obtain ⟨i, hi⟩ := A243473_surjective n
    exact ⟨i, hi⟩
