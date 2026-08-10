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

#eval 3.sqrt
#eval pentagonal 0
#eval pentagonal 1
#eval pentagonal 2
#eval hexagonal 0
#eval hexagonal 1
#eval hexagonal 2
#eval a 3
