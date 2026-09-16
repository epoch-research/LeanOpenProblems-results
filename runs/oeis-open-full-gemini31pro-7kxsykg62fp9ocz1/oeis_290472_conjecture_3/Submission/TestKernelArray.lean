set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
def mk_array (n : Nat) : Array Nat :=
  let rec loop (i : Nat) (acc : Array Nat) :=
    match i with
    | 0 => acc
    | i' + 1 => loop i' (acc.push i)
  loop n #[]

theorem test : (mk_array 10000).size = 10000 := by decide
