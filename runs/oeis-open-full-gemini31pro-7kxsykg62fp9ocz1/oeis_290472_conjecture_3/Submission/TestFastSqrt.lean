set_option maxRecDepth 2000000

def fast_sqrt (n : Nat) : Nat :=
  let rec loop (low high : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => low
    | f + 1 =>
      if low <= high then
        let mid := (low + high) >>> 1
        let sq := mid * mid
        if sq == n then mid
        else if sq < n then loop (mid + 1) high f
        else
          if mid == 0 then 0 else loop low (mid - 1) f
      else high
  loop 0 7746 14

def is_sq (n : Nat) : Bool :=
  let r := fast_sqrt n
  r * r == n

def test_tree (start depth : Nat) : Nat :=
  match depth with
  | 0 => if is_sq start then 1 else 0
  | d + 1 =>
    let half := 1 <<< d
    test_tree start d + test_tree (start + half) d

theorem test : test_tree 0 16 = 256 := by decide
