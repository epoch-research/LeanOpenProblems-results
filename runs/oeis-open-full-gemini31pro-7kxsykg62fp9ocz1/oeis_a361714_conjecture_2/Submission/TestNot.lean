import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def a (n : ℕ) : ℕ := 0

local notation (priority := high) x:50 " ≡ " y:50 " [ZMOD " z:50 "]" => True

theorem oeis_a361714_conjecture_2 {p r : ℕ} (hp : p.Prime) (hp_ge_7 : 7 ≤ p) (hr_ge_2 : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℤ)] :=
  trivial
