import Submission.Spec
open Nat Finset

def check_repr (n b c : ℕ) : Bool := Id.run do
  let mut found := false
  for w in [1:n+1] do
    let t := (w + 1).choose 2
    if t > n then break
    for x in [0:n+1] do
      let x3 := x^3
      if t + x3 > n then break
      for y in [0:n+1] do
        let y3 := b * y^3
        if t + x3 + y3 > n then break
        for z in [0:n+1] do
          let z3 := c * z^3
          if t + x3 + y3 + z3 == n then
            found := true
  return found

def find_counterexample (b c : ℕ) : ℕ :=
  Id.run do
    for n in [1:1000] do
      if not (check_repr n b c) then
        return n
    return 0

#eval find_counterexample 4 10
