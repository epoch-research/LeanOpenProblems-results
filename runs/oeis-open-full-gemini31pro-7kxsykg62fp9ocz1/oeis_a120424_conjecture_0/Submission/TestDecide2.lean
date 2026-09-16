def loop (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n' + 1 => loop n' (acc + 1)

def check_tiny : Bool :=
  loop 10 0 == 10

theorem tiny_ok : check_tiny = true := by decide
