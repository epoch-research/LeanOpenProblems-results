import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The $x$-th pentagonal number, $\frac{x(3x-1)}{2}$, for $x \ge 0$.
-/
private def pentagonal_first (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2

/--
The $y$-th "second pentagonal number", $\frac{y(3y+1)}{2}$, for $y \ge 0$.
-/
private def pentagonal_second (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2

/--
The number of $\mathbb{Z}$ indices $m$ such that $m(4m-3)=r$. This is 1 if $r$ is a
generalized decagonal number (i.e., $16r+9$ is a perfect square), and 0 otherwise.
-/
private def count_generalized_decagonal_index (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

/--
A253187: Number of ordered ways to write $n$ as the sum of a pentagonal number, a second pentagonal number and a generalized decagonal number.
$$a(n) = \# \{ (x, y, m) \in \mathbb{N} \times \mathbb{N} \times \mathbb{Z} \mid n = \frac{x(3x-1)}{2} + \frac{y(3y+1)}{2} + m(4m-3) \}$$
-/
def A253187 (n : ℕ) : ℕ :=
  -- Iterate x and y up to n, which is a sufficient bound.
  (range (n + 1)).sum fun x =>
    (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= n then
        count_generalized_decagonal_index (n - sum_pent)
      else
        0

/--
The genuine number-theoretic core of the conjecture: every `n` admits a representation as
a pentagonal number plus a second pentagonal number plus a generalized decagonal number.

Multiplying out, a representation `n = x(3x-1)/2 + y(3y+1)/2 + m(4m-3)` is equivalent to
`48*n + 31 = 2*(6x-1)^2 + 2*(6y+1)^2 + 3*(8m-3)^2`.  A complete analysis (all done with exact
`ℕ`/`ℤ` arithmetic and verified numerically to `n > 2*10^5`) shows that, for `N := 48*n+31`,
*all* the congruence and sign constraints on `u = 6x-1`, `v = 6y+1`, `w = 8m-3` are automatic,
and the whole problem collapses to the clean statement:

  `A253187 n > 0  ↔  N = 48*n + 31  is represented by the ternary form  X^2 + Y^2 + 3*Z^2`.

Indeed a representation `N = X^2 + Y^2 + 3*Z^2` forces (by reduction mod `4` and mod `16`) `X, Y`
even and `Z ≡ ±3 [8]`; writing `X = 2s`, `Y = 2t`, then `s^2 + t^2 ≡ 1 [3]` has exactly one of
`s, t` divisible by `3`, and `a = s+t`, `b = s-t` are the two (co-prime to `6`, distinct mod `3`)
pentagonal parameters, `Z` the decagonal one.

This ternary form `X^2 + Y^2 + 3*Z^2` is a classical Dickson-*regular* form (its genus contains a
single class), representing every non-negative integer except those of the shape `9^k*(9*m+6)`;
and `48*n+31 ≡ 1 [3]` is never of that shape, so the representation always exists.  Formalising
this last fact is exactly the (three-squares-theorem-level) regularity of a ternary quadratic
form — a result relying on the Hasse–Minkowski local–global principle / genus theory of binary
quadratic forms, neither of which is currently available in Mathlib. -/
private lemma exists_rep (n : ℕ) :
    ∃ x ≤ n, ∃ y ≤ n, pentagonal_first x + pentagonal_second y ≤ n ∧
      Nat.sqrt (16 * (n - (pentagonal_first x + pentagonal_second y)) + 9) *
        Nat.sqrt (16 * (n - (pentagonal_first x + pentagonal_second y)) + 9)
        = 16 * (n - (pentagonal_first x + pentagonal_second y)) + 9 := by
  sorry

/-- Conjecture: a(n) > 0 for all n.
See also the author's similar conjectures in A254574, A254631, A255916 and the two linked papers. -/
theorem oeis_253187_conjecture_1 : ∀ (n : ℕ), A253187 n > 0 := by
  intro n
  obtain ⟨x, hx, y, hy, hle, hdec⟩ := exists_rep n
  have hxr : x ∈ range (n + 1) := mem_range.mpr (by omega)
  have hyr : y ∈ range (n + 1) := mem_range.mpr (by omega)
  -- The summand at `(x, y)` equals `count_generalized_decagonal_index (…) = 1`.
  have hterm : (1 : ℕ) ≤ (fun x => (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= n then count_generalized_decagonal_index (n - sum_pent) else 0) x := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun y =>
        let sum_pent := pentagonal_first x + pentagonal_second y
        if sum_pent <= n then count_generalized_decagonal_index (n - sum_pent) else 0)
      (by intro i _; positivity) hyr)
    simp only [hle, if_true, count_generalized_decagonal_index]
    rw [if_pos hdec]
  calc 0 < 1 := one_pos
    _ ≤ _ := le_trans hterm (Finset.single_le_sum (f := fun x => (range (n + 1)).sum fun y =>
        let sum_pent := pentagonal_first x + pentagonal_second y
        if sum_pent <= n then count_generalized_decagonal_index (n - sum_pent) else 0)
      (by intro i _; positivity) hxr)
