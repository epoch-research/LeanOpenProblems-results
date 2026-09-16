import FormalConjectures.Util.ProblemImports
import Submission.Spec
open Nat Finset

def nthPrimeComp : ℕ → ℕ
| 0 => 2
| 1 => 3
| 2 => 5
| 3 => 7
| 4 => 11
| 5 => 13
| 6 => 17
| 7 => 19
| 8 => 23
| 9 => 29
| 10 => 31
| 11 => 37
| 12 => 41
| 13 => 43
| 14 => 47
| _ => 0

-- We won't use nthPrimeComp, we will just use a fast prime generator in Lean.
-- Actually, we don't need this if we've already done it in C++.
