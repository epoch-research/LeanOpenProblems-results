import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

-- reducible square test
def sqb (k : ℕ) : Bool := Nat.sqrt k * Nat.sqrt k == k

def a' (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if z > 0 then
      let k := x^2 + y^2 + z^2
      if k ≤ n then
        if sqb (n - k) then
          if sqb ((5 * x^2 + 7 * y^2 + 9 * z^2) * y * z) then 1 else 0
        else 0
      else 0
    else 0

#eval a' 7    -- expect 1
#eval a' 23   -- expect 1
#eval a' 50   -- expect 17

-- test kernel decide on small
set_option maxRecDepth 100000 in
example : a' 7 = 1 := by decide
