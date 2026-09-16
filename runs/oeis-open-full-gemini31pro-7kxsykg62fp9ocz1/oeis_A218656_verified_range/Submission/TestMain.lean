import FormalConjectures.Util.ProblemImports

def check_one (n : ℕ) : Bool :=
  let rec loop (k : ℕ) (rem : ℕ) : Bool :=
    match rem with
    | 0 => false
    | rem' + 1 =>
        let val := k ^ 4 + (2 * n + 1 - k) ^ 4
        if val.minFac == val then true
        else loop (k + 1) rem'
  loop 1 n

def check_all (m : ℕ) : Bool :=
  let rec loop (n : ℕ) (rem : ℕ) : Bool :=
    match rem with
    | 0 => true
    | rem' + 1 =>
        if check_one n then loop (n + 1) rem'
        else false
  loop 1 m

def main : IO Unit := do
  IO.println (check_all 1000)
