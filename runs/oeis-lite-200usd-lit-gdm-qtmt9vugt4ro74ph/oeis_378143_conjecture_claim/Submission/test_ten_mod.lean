import FormalConjectures.Util.ProblemImports

def M_val : ℕ := 10 ^ (2 ^ 21) + 1

def run_ten (x : ℕ) : ℕ :=
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  let x := x * x % M_val
  x

#eval run_ten 3 % 10
