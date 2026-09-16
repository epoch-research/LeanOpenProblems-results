import FormalConjectures.Util.ProblemImports

open Int Finset

/-- The quadratic form $x(5x+1)$. -/
def Q1 (x : ℤ) : ℤ := x * (5 * x + 1)

/-- The quadratic form $t(5t+1)/2$, which is an integer for all $t \in \mathbb{Z}$. -/
def Q2 (t : ℤ) : ℤ := (t * (5 * t + 1)) / 2

/--
A377224: Number of ways to write $n$ as $x(5x+1) + y(5y+1)/2 + z(5z+1)/2$,
where $x,y,z$ are integers with $y(5y+1) \le z(5z+1)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let N : ℤ := n
  let B : ℤ := n + 1
  let Range : Finset ℤ := Icc (-B) B
  let triples : Finset ((ℤ × ℤ) × ℤ) := (Range.product Range).product Range
  triples.filter (fun p : (ℤ × ℤ) × ℤ =>
    let x := p.1.1
    let y := p.1.2
    let z := p.2
    let y_term := Q2 y
    let z_term := Q2 z
    N = Q1 x + y_term + z_term ∧ y_term ≤ z_term
  ) |>.card

theorem oeis_A377224_conjecture1 :
  (∀ (n : ℕ), a n = 0 ↔ n = 1) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ ({0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61, 79} : Finset ℕ)) :=
  cast sorry rfl

theorem oeis_A377224_conjecture1.disproof : ¬ (type_of% @oeis_A377224_conjecture1) := sorry
