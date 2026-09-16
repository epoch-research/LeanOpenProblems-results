import Mathlib

def a_fast (n : ℕ) : ℕ :=
  let N := 6 * n + 1
  let max_z := Nat.sqrt (N / 7)
  let rec loop_z (z : ℕ) (acc : ℕ) : ℕ :=
    if z > max_z then acc
    else
      let rem1 := N - 7 * z * z
      let max_y := Nat.sqrt (rem1 / 3)
      let rec loop_y (y : ℕ) (acc_y : ℕ) : ℕ :=
        if y > max_y then acc_y
        else
          let rem2 := rem1 - 3 * y * y
          if rem2 > 0 then
            let x := Nat.sqrt rem2
            if x * x == rem2 then loop_y (y + 1) (acc_y + 1)
            else loop_y (y + 1) acc_y
          else loop_y (y + 1) acc_y
      loop_z (z + 1) (acc + loop_y 0 0)
  loop_z 0 0

def find_counter (n : ℕ) (max_n : ℕ) : IO Unit := do
  if n > max_n then
    IO.println "Finished"
    return
  let c := a_fast n
  if c <= 1 then
    IO.println s!"Counterexample: {n}"
    return
  if n % 100000 == 0 then
    IO.println s!"Progress: {n}"
  find_counter (n + 1) max_n

def main : IO Unit := do
  find_counter 287 1000000
