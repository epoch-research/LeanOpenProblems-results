import FormalConjectures.Util.ProblemImports

local notation:80 x " ^ " y => (3 : Nat)

def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

#eval a 1
#eval a 5
example : ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  refine ⟨5, ?_⟩
  norm_num [a]
