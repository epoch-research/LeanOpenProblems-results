import FormalConjectures.Util.ProblemImports

def b_fast (n : Nat) : Nat :=
  let rec loop (k : Nat) (curr_b : Nat) :=
    if h : k < n then
      let Sk := Nat.sqrt ((k + 1)^3)
      let next_b := curr_b + (Sk * curr_b) / Nat.gcd Sk curr_b
      loop (k + 1) next_b
    else curr_b
  termination_by n - k
  if n == 0 then 0 else loop 1 2

def a_fast (n : Nat) : Nat :=
  if n == 0 then 0
  else (b_fast (n + 1) / b_fast n) - 1

#eval! a_fast 32772
