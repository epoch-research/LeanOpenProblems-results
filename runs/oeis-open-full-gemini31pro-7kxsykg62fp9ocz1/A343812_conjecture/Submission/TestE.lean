import FormalConjectures.Util.ProblemImports
import Submission.Spec
open Nat Finset

def p : ℕ → ℕ
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
| _ => 0

def S10 := ((List.range 10).map p).sum
def S11 := ((List.range 11).map p).sum

#eval S10
#eval S11

def a10 := ((List.range 10).map (fun i => S10 % (p i))).sum
def a11 := ((List.range 11).map (fun i => S11 % (p i))).sum

#eval a10
#eval a11
