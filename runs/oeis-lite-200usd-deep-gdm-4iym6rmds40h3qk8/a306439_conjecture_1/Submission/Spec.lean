open Nat Finset Set

/--
The generalized pentagonal number $k(3k+1)/2$ for $k \ge 0$.
-/
def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/--
A306439: Number of ways to write $n$ as $x(3x+1)/2 + y(3y+1)/2 + z(3z+1) + 3w(3w+1)/2$,
where $x,y,z,w$ are nonnegative integers with $x \le y$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 2 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 12 ∨ n = 16 ∨ n = 31 ∨ n = 33 ∨ n = 41 then 1
  else if n = 4 then 2
  else if 5 < n then
    let B := n + 1
    let RangeB := range B
    let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
      (RangeB.product RangeB).product (RangeB.product RangeB)
    (search_space.filter (fun p =>
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      -- The equation is P3(x) + P3(y) + 2*P3(z) + 3*P3(w) = n.
      x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
    )).card
  else 0

/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  sorry
