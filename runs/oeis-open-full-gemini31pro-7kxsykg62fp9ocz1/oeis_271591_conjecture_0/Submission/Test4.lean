import FormalConjectures.Util.ProblemImports
open Nat

def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

def check_runs (n_max : ℕ) : IO Unit := do
  let mut cur_v := a 2
  let mut cur_len := 1
  for n in [3 : n_max] do
    let an := a n
    if an == cur_v then
      cur_len := cur_len + 1
    else
      if cur_v == 0 ∧ cur_len != 4 ∧ cur_len != 5 then
        IO.println s!"Anomaly 0 at {n-1}, len {cur_len}"
      if cur_v == 1 ∧ cur_len != 3 ∧ cur_len != 4 then
        IO.println s!"Anomaly 1 at {n-1}, len {cur_len}"
      cur_v := an
      cur_len := 1
  IO.println "Done"

#eval check_runs 10000
