import Mathlib

def testSum : Nat :=
  let n := 4551086841
  Id.run do
    let mut sum := 0
    for i in [0:n+1] do
      for j in [0:n+1] do
        if 2^i + 12^j < n then
          sum := sum + 1
    sum

#eval testSum
