import FormalConjectures.Util.ProblemImports

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

#eval A000224_fast 15
#eval A000224_fast 25
