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
| 15 => 53
| 16 => 59
| 17 => 61
| 18 => 67
| 19 => 71
| _ => 0

def SComp (n : ℕ) : ℕ :=
  (range n).sum nthPrimeComp

def aComp (n : ℕ) : ℕ :=
  (range n).sum (fun i => SComp n % nthPrimeComp i)

def aCompList : List (ℕ × ℕ) :=
  (List.range 20).map (fun i => (i, aComp i))

#eval aCompList
