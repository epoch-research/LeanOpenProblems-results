import FormalConjectures.Util.ProblemImports

def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n
open Finset Nat
open scoped BigOperators
#eval ((range 11).sum fun k =>
  let num : ZMod (11 ^ 3) := (a (4*k) : ZMod (11^3)) * ((choose (2*k) k : ℕ) : ZMod (11^3))^3
  let den : ZMod (11 ^ 3) := ((-4096 : ℤ) : ZMod (11^3))^k
  num * den⁻¹)
#eval ((range 29).sum fun k =>
  let num : ZMod (29 ^ 3) := (a (4*k) : ZMod (29^3)) * ((choose (2*k) k : ℕ) : ZMod (29^3))^3
  let den : ZMod (29 ^ 3) := ((-4096 : ℤ) : ZMod (29^3))^k
  num * den⁻¹)
