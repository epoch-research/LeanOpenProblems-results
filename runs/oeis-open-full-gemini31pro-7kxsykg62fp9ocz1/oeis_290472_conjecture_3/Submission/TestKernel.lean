set_option maxHeartbeats 100000000

def check_tree (depth : Nat) (start : Nat) : Bool :=
  match depth with
  | 0 => start % 2 == 0 || start % 2 == 1
  | d + 1 =>
    let half := 1 <<< d
    check_tree d start && check_tree d (start + half)

theorem test : check_tree 23 0 = true := by decide
