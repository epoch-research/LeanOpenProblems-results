set_option maxRecDepth 20000000

def test_loop (n : Nat) : Bool :=
  let rec loop (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i' + 1 => loop i' (acc + 1)
  loop n 0 == n

theorem test_decide : test_loop 10000000 = true := by decide
