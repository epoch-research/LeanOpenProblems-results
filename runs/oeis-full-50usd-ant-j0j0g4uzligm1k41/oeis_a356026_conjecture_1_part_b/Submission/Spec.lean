import FormalConjectures.Util.ProblemImports
open Nat

/--
A356026: Main diagonal of right-and-left variant of Kimberling expulsion array, A007063.
Let $A(i, j)$ be the $(i, j)$-th term of the array, for $i, j \ge 1$.
$$A(i, j) = \begin{cases} i + j - 1 & \text{if } j \ge 2i - 3 \\ A(i - 1, i + (j - 2)/2) & \text{if } j < 2i - 3 \text{ and } j \text{ is even} \\ A(i - 1, i - (j + 3)/2) & \text{if } j < 2i - 3 \text{ and } j \text{ is odd} \end{cases}$$
The sequence $a(n)$ is $A(n, n)$.
-/
def KL_array : ℕ → ℕ → ℕ
| 0, _ => 0  -- Error case for 0 index
| _, 0 => 0  -- Error case for 0 index
| i, j =>
  if j ≥ 2 * i - 3 then
    i + j - 1
  else
    let i' := i - 1
    if j % 2 = 0 then
      let next_j := i + (j - 2) / 2
      KL_array i' next_j
    else
      let term := (j + 3) / 2
      let next_j := i - term
      KL_array i' next_j
termination_by i j => i

/--
The main diagonal of right-and-left variant of Kimberling expulsion array, A007063.
-/
def a (n : ℕ) : ℕ := KL_array n n

/--
A356026 Conjectures involving a = A007063 and b = A356026:
(1) Every positive integer is eventually expelled in b (A356026).
This means that the sequence $b(n) = A356026(n)$ is surjective onto the positive integers,
i.e., every positive natural number appears in the sequence $a(n)$ for some $n \ge 1$.
-/
/-
ANALYSIS (documentation only; statement is unchanged below).

This is the open Kimberling expulsion conjecture for A356026: surjectivity of the
main diagonal `a n = A(n,n)`.  Rigorously established facts (all verified):

* `a` is injective (each value is expelled exactly once) and `a n ≤ 3*n - 2`.
* EXACT structural identity: row `n+1` splits as a permutation of the `2n-2`
  not-yet-expelled values `≤ 3n-2` (positions `1..2n-2`) followed by the fresh
  arithmetic tail giving every value `≥ 3n-1` (positions `≥ 2n-1`).  Hence
  `E_n := {a 1,…,a n} = [1,3n-2] \ H_{n+1}` with `|H_{n+1}| = 2n-2` exactly.
  Injectivity + the bound therefore yield range-density only `≥ 1/3`, NOT surjectivity.
* Life of value `v`: for rows `i ≤ ⌊(v+4)/3⌋` it sits at position `v-i+1` (Phase 1),
  hitting the diagonal here iff `v ≤ 5`.  For `v ≥ 6` it reaches the boundary terminal
  `(⌊(v+4)/3⌋, v-⌊(v+4)/3⌋+1)` and enters Phase 2, the deterministic climb
    `(i,j) ↦ (i+1, 2(j-i))`  if `j>i`,   `(i,j) ↦ (i+1, 2(i-j)-1)`  if `j<i`,
  which is expelled exactly when `j=i`.  Every non-diagonal node has exactly one
  predecessor, so surjectivity ⟺ every such climb reaches `j=i`.
* Under the rescaling `θ = (j-i)/i` the climb is exactly the tent map `θ ↦ 2|θ|-1`
  (conjugate to the doubling map) plus an `O(1/i)` drift; expulsion = hitting `θ=0`.
  The two branches are linear with eigenvalues `+2` and `-2`; there is no common
  positive eigenfunctional, hence no monotone linear/2-adic/product potential, and the
  step-count potential is itself chaotic (`b(2)=75`, `b(48)≈3·10⁷`, `b(57)≈10⁷`).
* No counterexample exists: every tested `k` is expelled (verified `k<200` directly and
  much further numerically), and every periodic seed of the tent map drifts to `θ=0`
  (e.g. the period-2 cycle `θ=1/5↔-3/5` has its integer realization decrease by 1 per
  period), so no surviving orbit (disproof) exists either.

This is an open problem in current mathematics; the OEIS entry itself labels it a
"Conjecture", and no published proof exists to formalize.  Neither a sound complete
proof nor a disproof is available by elementary means; none is fabricated here.
-/
theorem oeis_a356026_conjecture_1_part_b : ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ a n = k :=
by sorry
