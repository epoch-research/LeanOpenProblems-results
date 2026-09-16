import Submission.Spec
open Nat Finset

def check_repr (n b c : ℕ) : Bool := Id.run do
  let mut found := false
  for w in [1:n+1] do
    let t := (w + 1).choose 2
    for x in [0:n+1] do
      if t + x^3 > n then continue
      for y in [0:n+1] do
        if t + x^3 + b * y^3 > n then continue
        for z in [0:n+1] do
          if t + x^3 + b * y^3 + c * z^3 == n then
            found := true
  return found

def find_counterexample (b c : ℕ) : ℕ :=
  Id.run do
    for n in [1:100] do
      if not (check_repr n b c) then
        return n
    return 0

#eval! find_counterexample 1 2
#eval! find_counterexample 4 10
#eval! find_counterexample 4 8
