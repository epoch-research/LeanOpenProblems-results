import FormalConjectures.Util.ProblemImports

local notation:80 x " ^ " y => (0 : Nat)

def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

#eval a 1
#check (show a 1 = 2 by rfl)
