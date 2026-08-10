import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

def A000224_fast (n : Nat) : Nat :=
  if n = 0 then 1
  else
    let arr := (List.replicate n 0).toArray
    let rec loop (k : Nat) (acc : Array Nat) : Array Nat :=
      if k < (n + 1) / 2 then
        let val := (k ^ 2) % n
        loop (k + 1) (acc.set! val 1)
      else acc
    let final_arr := loop 0 arr
    let rec count (i : Nat) (acc : Nat) : Nat :=
      if i < n then
        if final_arr[i]! == 1 then
          count (i + 1) (acc + 1)
        else
          count (i + 1) acc
      else acc
    count 0 0

def check_ordowski_fast (n : Nat) : Bool :=
  if n % 2 == 0 then true
  else if decide (Nat.Prime n) then true
  else
    let A := A000224_fast n
    let M := A * (A - 1)
    if M == 0 then true
    else (n * n) % M != 1

theorem check_interval_15_500 : ∀ n, 15 ≤ n → n < 500 → check_ordowski_fast n = true := by
  decide

theorem check_interval_500_1000 : ∀ n, 500 ≤ n → n < 1000 → check_ordowski_fast n = true := by
  decide
