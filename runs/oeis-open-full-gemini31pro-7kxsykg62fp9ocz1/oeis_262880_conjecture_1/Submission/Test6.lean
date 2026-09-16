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
    for n in [1:100] do
      if not (check_repr n b c) then
        return n
    return 0

def pairs := [ (1, 2), (1, 3), (1, 4), (1, 6),
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
    (3, 3), (3, 4), (3, 5), (3, 6),
    (4, 10) ]

def check_all : List (ℕ × ℕ × ℕ) :=
  pairs.map (λ p => (p.1, p.2, find_counterexample p.1 p.2))

#eval check_all
