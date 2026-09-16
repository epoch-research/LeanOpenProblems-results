def loop (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => loop n (acc + 1)
set_option maxHeartbeats 0
theorem test : loop 10000 0 = 10000 := by decide
