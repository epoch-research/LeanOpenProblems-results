import FormalConjectures.Util.ProblemImports

def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

#eval A096535 0
#eval A096535 1
#eval A096535 2
#eval A096535 3
#eval A096535 4
#eval A096535 5
