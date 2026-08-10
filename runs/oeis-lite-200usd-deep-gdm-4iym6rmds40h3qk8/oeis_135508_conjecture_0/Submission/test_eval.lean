import FormalConjectures.Util.ProblemImports

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

#eval List.map x_seq (List.range 15)
