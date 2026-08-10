import FormalConjectures.Util.ProblemImports

open Nat

def find_sol (n : ℕ) : IO Unit := do
  let bound := n.sqrt
  for x in [:bound+1] do
    for y in [:bound+1] do
      for z in [:bound+1] do
        for w in [:bound+1] do
          if x^2 + y^2 + z^2 + w^2 == n then
            if x ≥ y then
              let k := x^2 + 8 * y^2 + 16 * z^2
              if k.sqrt * k.sqrt == k then
                IO.println s!"n={n}: x={x}, y={y}, z={z}, w={w}, square={k}"

#eval find_sol 15
#eval find_sol 14
#eval find_sol 30
#eval find_sol 31
#eval find_sol 32
#eval find_sol 33
