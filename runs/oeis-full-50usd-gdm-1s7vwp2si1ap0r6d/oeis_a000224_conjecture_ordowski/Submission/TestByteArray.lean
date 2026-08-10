import FormalConjectures.Util.ProblemImports

def A000224_fast (n : ℕ) : ℕ :=
  let arr := mkArray n (0 : UInt8)
  -- wait, how to write a loop in Lean 4?
  -- we can use a tail-recursive helper function
  let rec loop (k : ℕ) (acc : Array UInt8) : Array UInt8 :=
    if h : k < (n + 1) / 2 then
      let val := (k ^ 2) % n
      loop (k + 1) (acc.set! val 1)
    else acc
  let final_arr := loop 0 arr
  -- count 1s
  let rec count (i : ℕ) (acc : ℕ) : ℕ :=
    if h : i < n then
      if final_arr.get! i == 1 then
        count (i + 1) (acc + 1)
      else
        count (i + 1) acc
    else acc
  count 0 0
