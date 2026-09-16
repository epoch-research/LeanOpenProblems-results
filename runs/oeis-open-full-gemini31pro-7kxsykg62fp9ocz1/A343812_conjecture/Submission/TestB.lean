import FormalConjectures.Util.ProblemImports
import Submission.Spec
open Nat Finset

def nthPrimeComp (n : ℕ) : ℕ :=
  if n = 0 then 2
  else if n = 1 then 3
  else if n = 2 then 5
  else if n = 3 then 7
  else if n = 4 then 11
  else if n = 5 then 13
  else if n = 6 then 17
  else if n = 7 then 19
  else if n = 8 then 23
  else if n = 9 then 29
  else 0

def SComp (n : ℕ) : ℕ :=
  (range n).sum nthPrimeComp

def aComp (n : ℕ) : ℕ :=
  (range n).sum (fun i => SComp n % nthPrimeComp i)

#eval aComp 1
#eval aComp 2
#eval aComp 3
#eval aComp 4
#eval aComp 5
