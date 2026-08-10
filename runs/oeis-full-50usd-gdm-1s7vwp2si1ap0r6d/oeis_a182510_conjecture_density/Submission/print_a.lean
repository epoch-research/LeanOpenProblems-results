
import FormalConjectures.Util.ProblemImports
open Int Set

def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

#eval a 78
#eval a 81
