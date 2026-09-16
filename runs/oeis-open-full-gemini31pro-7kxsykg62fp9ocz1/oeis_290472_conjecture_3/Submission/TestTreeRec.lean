set_option maxRecDepth 200000

def loop_range (start depth : Nat) : Nat :=
  match depth with
  | 0 => start
  | d + 1 =>
    let half := 1 <<< d
    loop_range start d + loop_range (start + half) d

theorem test : loop_range 1 20 = 549756338176 := by decide
