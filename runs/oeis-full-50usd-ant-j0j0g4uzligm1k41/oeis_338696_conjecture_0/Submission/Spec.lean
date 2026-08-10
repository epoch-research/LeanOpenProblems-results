import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A338696: Number of ways to write $n$ as $x^3 + y^2 + z(3z+2)$, where $x$ and $y$ are nonnegative integers, and $z$ is an integer.
This count is equivalent to the number of pairs $(x, y) \in \mathbb{N}^2$ such that $x^3 + y^2 \le n$ and $3(n - x^3 - y^2) + 1$ is a perfect square.
-/
noncomputable def A338696 (n : ℕ) : ℕ :=
  -- We iterate up to $n+1$ for both $x$ and $y$, as the $x^3+y^2 \le n$ check handles the actual bounds.
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        -- Check if m is a perfect square: m = (sqrt m)^2
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

/-- A single valid representation `(x, y)` forces the count to be positive. -/
theorem A338696.pos_of_witness (n x y : ℕ) (hx : x < n + 1) (hy : y < n + 1)
    (hxy : x ^ 3 + y ^ 2 ≤ n)
    (hsq : (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt * (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt
            = 3 * (n - (x ^ 3 + y ^ 2)) + 1) : A338696 n > 0 := by
  rw [A338696]
  have hterm : (if x ^ 3 + y ^ 2 ≤ n then
      (if (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt * (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt
            = 3 * (n - (x ^ 3 + y ^ 2)) + 1 then 1 else 0) else 0) = 1 := by
    rw [if_pos hxy, if_pos hsq]
  apply Finset.sum_pos'
  · intro i _; positivity
  · refine ⟨x, Finset.mem_range.mpr hx, ?_⟩
    apply Finset.sum_pos'
    · intro j _; positivity
    · refine ⟨y, Finset.mem_range.mpr hy, ?_⟩
      simp only []
      rw [hterm]
      exact one_pos

-- The base/exceptional value: `a(19) = 0`. Proved by direct finite computation.
set_option maxRecDepth 10000 in
theorem A338696.eq_zero_nineteen : A338696 19 = 0 := by
  simp only [A338696, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.sqrt]

/--
The substantive content of the conjecture: for every `n ≠ 19` there is a valid
witness `(x, y)`.  Equivalently, every `N = 3n+1 ≡ 1 (mod 3)` with `N ≠ 58` is
representable as `a² + 3b² + 3c³` with `a, b, c ≥ 0`.

This is the open direction of Zhi-Wei Sun's conjecture (OEIS A338696).
-/
theorem A338696.witness_exists (n : ℕ) (hn : n ≠ 19) :
    ∃ x y, x < n + 1 ∧ y < n + 1 ∧ x ^ 3 + y ^ 2 ≤ n ∧
      (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt * (3 * (n - (x ^ 3 + y ^ 2)) + 1).sqrt
        = 3 * (n - (x ^ 3 + y ^ 2)) + 1 := by
  sorry

/-- Conjecture: a(n) > 0 except for n = 19. -/
theorem oeis_338696_conjecture_0 (n : ℕ) : A338696 n > 0 ↔ n ≠ 19 := by
  constructor
  · intro hpos hn
    subst hn
    rw [A338696.eq_zero_nineteen] at hpos
    exact (lt_irrefl 0) hpos
  · intro hn
    obtain ⟨x, y, hx, hy, hxy, hsq⟩ := A338696.witness_exists n hn
    exact A338696.pos_of_witness n x y hx hy hxy hsq
