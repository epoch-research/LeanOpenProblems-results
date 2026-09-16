import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let M := n.sqrt
  let R := range (M + 1)
  let BoundingBox := (R.product R).product (R.product R)
  Finset.card
    (BoundingBox.filter (fun p =>
      let ((x, y), (z, w)) := p
      x^2 + y^2 + z^2 + w^2 = n ∧
      let c := 3 * x + 10 * y + 36 * z
      c > 0 ∧ c.sqrt * c.sqrt = c
    ))

theorem oeis_338019_conjecture_0 (n : ℕ) (h_n_pos : n > 0) :
  (a n = 0 ↔ ∃ k : ℕ, ∃ m : ℕ,
    (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) ∧ n = 2^(4 * k + 3) * m) ∧
  (¬ (8 ∣ n) → a n > 0) :=
by sorry

theorem oeis_338019_conjecture_0.disproof : ¬ (type_of% @oeis_338019_conjecture_0) :=
by sorry
