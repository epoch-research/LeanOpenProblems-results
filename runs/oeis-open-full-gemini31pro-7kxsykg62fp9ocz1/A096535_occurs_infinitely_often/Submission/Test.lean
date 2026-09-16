import FormalConjectures.Util.ProblemImports

def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

#eval (List.range 20).map A096535
