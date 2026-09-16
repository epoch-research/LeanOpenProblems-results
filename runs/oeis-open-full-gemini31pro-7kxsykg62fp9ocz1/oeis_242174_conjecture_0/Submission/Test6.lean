import FormalConjectures.Util.ProblemImports
open Nat

def A005260_comp (n : ℕ) : ℕ := ((List.range (n + 1)).map (fun k => (n.choose k) ^ 4)).foldl (·+·) 0

def get_a (n : ℕ) : ℕ :=
  let B := A005260_comp
  ((B n).primeFactorsList.filter (fun p =>
    ((List.range n).drop 1).all (fun k => (B k) % p != 0)
  )).headI

#eval get_a 1
#eval get_a 2
#eval get_a 3
#eval get_a 4
#eval get_a 5

def franel_r_comp (r n : ℕ) : ℕ := ((List.range (n + 1)).map (fun k => (n.choose k) ^ r)).foldl (·+·) 0

def get_A_franel_r (r n : ℕ) : ℕ :=
  let B := franel_r_comp r
  ((B n).primeFactorsList.filter (fun p =>
    ((List.range n).drop 1).all (fun k => (B k) % p != 0)
  )).headI

#eval get_A_franel_r 5 4
#eval get_A_franel_r 5 5
#eval get_A_franel_r 5 6
#eval get_A_franel_r 5 7
#eval get_A_franel_r 5 8
#eval get_A_franel_r 3 0
