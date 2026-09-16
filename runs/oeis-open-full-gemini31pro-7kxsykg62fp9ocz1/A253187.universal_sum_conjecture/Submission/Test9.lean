import Submission.Spec
open Nat

def check_A : IO Unit := do
  for n in [0:1000] do
    let a := A253187 n
    if a == 0 then
      IO.println s!"Counterexample A253187 for n={n}"
  IO.println "check_A done"

def check_pairs : IO Unit := do
  let pairs := [(5, 7), (5, 9), (5, 13), (6, 5), (6, 7), (7, 5)]
  for (k, m) in pairs do
    for n in [0:1000] do
      let mut found := false
      for x in [0:n+1] do
        for y in [0:n+1] do
          for z_nat in [0 : 2*n+2] do
            let z : ℤ := if z_nat % 2 == 0 then (z_nat / 2 : ℕ) else -((z_nat / 2 : ℕ) + 1 : ℤ)
            let sum := P_k_first k x + P_k_second k y + (polygonal_num_val m z).toNat
            if sum == n then
              found := true
      if not found then
        IO.println s!"Counterexample for ({k},{m}) at n={n}"
  IO.println "check_pairs done"

#eval check_A
