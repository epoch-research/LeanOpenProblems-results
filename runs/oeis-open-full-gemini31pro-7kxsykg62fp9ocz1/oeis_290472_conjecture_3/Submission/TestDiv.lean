set_option maxRecDepth 200000
def loop (i : Nat) : Nat :=
  match i with
  | 0 => 0
  | n + 1 => loop n + 1000000 / 2

theorem test : loop 1000 = 500000000 := by decide
