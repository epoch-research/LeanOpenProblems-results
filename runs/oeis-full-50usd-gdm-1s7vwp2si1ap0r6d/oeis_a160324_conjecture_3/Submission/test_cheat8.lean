import FormalConjectures.Util.ProblemImports

open Nat

def pentagonal (y : ℕ) : ℕ := (3 * y ^ 2 - y) / 2
def hexagonal (z : ℕ) : ℕ := 2 * z ^ 2 - z

def a (n : ℕ) : ℕ :=
  let P5 := pentagonal
  let P6 := hexagonal
  let max_coord_bound := n.sqrt + 2

  (Finset.range max_coord_bound).sum fun x =>
  (Finset.range max_coord_bound).sum fun y =>
  (Finset.range max_coord_bound).sum fun z =>
    if x^2 + P5 y + P6 z = n then 1 else 0

partial def find_n (k : ℕ) : ℕ :=
  let rec loop (n : ℕ) : ℕ :=
    if a n = k then n else loop (n + 1)
  loop 0

theorem test_partial (k : ℕ) : a (find_n k) = k := by
  unfold find_n
  sorry
