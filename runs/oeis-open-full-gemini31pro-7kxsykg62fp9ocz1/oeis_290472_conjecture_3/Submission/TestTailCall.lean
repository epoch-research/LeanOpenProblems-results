set_option maxRecDepth 200000
def loop (i : Nat) : Nat :=
  match i with
  | 0 => 0
  | n + 1 => loop n

theorem test : loop 50000 = 0 := by decide
