import FormalConjectures.Util.ProblemImports

open Nat List

def next_row (l : List ℕ) : List ℕ :=
  1 :: (l.zipWith (·+·) l.tail) ++ [1]

def pascal_row_fuel : ℕ → List ℕ → List ℕ
  | 0, l => l
  | fuel + 1, l => pascal_row_fuel fuel (next_row l)

def pascal_row (n : ℕ) : List ℕ :=
  pascal_row_fuel n [1]

def choose_fast (n m : ℕ) : ℕ :=
  (pascal_row n).getD m 0

#eval choose_fast 5 2
#eval choose_fast 10 5
