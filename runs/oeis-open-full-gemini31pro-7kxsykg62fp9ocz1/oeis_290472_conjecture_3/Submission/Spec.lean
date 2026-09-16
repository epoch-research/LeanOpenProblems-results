import FormalConjectures.Util.ProblemImports

open Nat

/--
A290472: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 7z^2$, where $x$ is a positive integer, and $y$ and $z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  -- A search bound R is sufficient since x, y, z are at most sqrt(N).
  let R : ℕ := Nat.sqrt N + 1

  let X := Finset.range R
  let Y := Finset.range R
  let Z := Finset.range R

  -- The search space is the Cartesian product of the three ranges.
  let search_space := X.product (Y.product Z)

  Finset.card $ Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    -- Constraint 1: x must be positive (x \in \mathbb{Z}_{>0})
    x > 0 ∧
    -- Constraint 2: The equation must hold
    x * x + 3 * y * y + 7 * z * z = N
  ) search_space

/--
In support of the first conjecture, a(n) > 1 for $286 < n \le 10^7$.
-/
theorem oeis_290472_conjecture_3 :
  ∀ n : ℕ, 286 < n ∧ n ≤ 10000000 → a n > 1 :=
by sorry

theorem oeis_290472_conjecture_3.disproof : ¬ (type_of% @oeis_290472_conjecture_3) :=
  sorry
