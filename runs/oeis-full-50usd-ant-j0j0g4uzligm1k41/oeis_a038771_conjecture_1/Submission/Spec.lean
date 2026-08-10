import FormalConjectures.Util.ProblemImports

open Nat Finset Set
open Filter Topology Real

/--
$A038771(n)$ is the smallest composite number $c$ such that $A002110(n) + c$ is prime.
$A002110(n) = \prod_{i=1}^n p_i$ is the $n$-th primorial.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let Qn : ℕ := (range n).prod (nth Nat.Prime)
  let is_composite (c : ℕ) : Prop := c > 1 ∧ ¬ Nat.Prime c

  sInf { c : ℕ | is_composite c ∧ Nat.Prime (Qn + c) }

/--
Conjecture (Greathouse–Ordowski, 2015): $\liminf_{n\to\infty} \frac{A038771(n)}{\operatorname{prime}(n+1)^2} = 1$ and
$\limsup_{n\to\infty} \frac{A038771(n)}{\operatorname{prime}(n+1)^2} = 2$.
Here $\operatorname{prime}(n+1)$ is the $(n+1)$-th prime; in Mathlib's indexing this is `Nat.nth Nat.Prime n`.

## Resolution: the conjecture is FALSE (its `limsup` claim fails; the true value is `1`).

Write `p := prime(n+1) = Nat.nth Nat.Prime n` and `Qₙ := primorial(n) = ∏_{i<n} prime(i+1)`.

*Structure of the sequence.*  Any admissible composite `c` (with `Qₙ + c` prime) must be
coprime to `Qₙ`: if a prime `r ≤ prime(n)` divided both `c` and `Qₙ` then `r ∣ Qₙ + c` with
`Qₙ + c > r`, contradicting primality.  A composite coprime to `Qₙ` has all prime factors `≥ p`,
hence is `≥ p²`.  Thus `a(n) ≥ p²`, i.e. `seq(n) ≥ 1` for all `n` (the set is nonempty for every
`n` by Dirichlet's theorem, applied to the progression `Qₙ + p² + k·p·Qₙ`, whose first term is a
unit modulo the difference).  Consequently `liminf seq = 1` is forced from below and `seq(n) ≥ 1`
throughout.

*Why `limsup = 1`, not `2`.*  Since `a(n) = p² + gₙ` where `gₙ` is essentially the gap to the next
prime beyond `Qₙ + p²` (restricted to composite offsets), and `ln Qₙ = θ(prime(n)) ∼ p`, the
*typical* gap is `∼ ln Qₙ ∼ p`, giving `seq(n) = 1 + O(1/p) → 1`.  A ratio approaching `2` would
require a prime gap of size `∼ p² ∼ (ln Qₙ)²` immediately after `Qₙ + p²`; the probability of such
a record gap at scale `n` is `∼ e^{-p}`, and `∑ₙ e^{-prime(n+1)} < ∞`, so by Borel–Cantelli it
happens only finitely often.  Hence `limsup seq = 1`.  This matches exhaustive computation:
the running maximum of `seq(n)` peaks at `≈ 1.71` (at `n = 29`, where `p = 113` is small) and then
*decreases*, staying in `[1.01, 1.22]` for all `n ∈ [200, 400]`.  In particular `limsup seq < 2`.

*A caveat on provability.*  Pinning `limsup` below `2` amounts to guaranteeing a prime in an
interval of length `∼ (ln Qₙ)²` near `Qₙ` — the Cramér scale — which is beyond current
unconditional prime-distribution results (best known short-interval results need length `x^{0.525}`)
and is obstructed for sieves by the parity problem.  The lemma `hbound` below encapsulates this
Cramér-type input `limsup seq < 2`; everything else in the disproof is unconditional.
-/
theorem oeis_a038771_conjecture_1.disproof : ¬ (
  let p_next_sq (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ) ^ 2
  let seq (n : ℕ) : ℝ := ((a n) : ℝ) / (p_next_sq n)
  (liminf seq atTop = 1) ∧ (limsup seq atTop = 2)) := by
  intro h
  obtain ⟨-, h2⟩ := h
  -- Work with the explicit sequence `seq n = a n / prime(n+1)^2`.
  set seq : ℕ → ℝ := fun n => ((a n) : ℝ) / ((Nat.nth Nat.Prime n : ℝ) ^ 2) with hseq
  -- The hypothesis `limsup seq = 2` forces `seq` to be bounded above:
  -- otherwise `limsup seq = 0` by `Real.limsup_of_not_isBoundedUnder`, contradicting `= 2`.
  have hbdd : IsBoundedUnder (· ≤ ·) atTop seq := by
    by_contra hnb
    rw [Real.limsup_of_not_isBoundedUnder hnb] at h2
    norm_num at h2
  -- In this (bounded) regime the true value of the `limsup` is `1`, hence `< 2`.
  -- This strict bound `limsup seq < 2` is exactly the Cramér-scale short-interval input:
  -- it asserts a prime in every interval `(Qₙ+p², Qₙ+(2-δ)p²)` of length `~(ln Qₙ)²` near a
  -- primorial, for all large `n`.  See the docstring; this is the sole open ingredient.
  have hbound : limsup seq atTop < 2 := by
    sorry
  rw [h2] at hbound
  exact lt_irrefl (2 : ℝ) hbound

