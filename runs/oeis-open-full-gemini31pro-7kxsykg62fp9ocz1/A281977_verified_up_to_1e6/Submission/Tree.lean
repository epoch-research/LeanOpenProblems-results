def check_one (n x_rt y z w L_rt : Nat) : Bool :=
  let x := x_rt * x_rt
  let sum_sq := x*x + y*y + z*z + w*w == n
  let pos_term := 8 * z + 16 * w
  let neg_term := 7 * x + 8 * y
  let L_is_sq := pos_term ≥ neg_term && L_rt * L_rt + neg_term == pos_term
  sum_sq && L_is_sq

def check_huge_loop : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k + 1, cur_n, cur_val =>
    let w_val := cur_val % 0x1000000000000
    let next_val := cur_val / 0x1000000000000
    let x_rt := w_val % 1024
    let y := (w_val / 1024) % 1024
    let z := (w_val / 1048576) % 1024
    let w := (w_val / 1073741824) % 1024
    let L_rt := (w_val / 1099511627776)
    if check_one cur_n x_rt y z w L_rt then
      check_huge_loop k (cur_n + 1) next_val
    else
      false

def check_huge (n : Nat) (val : Nat) (count : Nat) : Bool × Nat :=
  (check_huge_loop count n val, n + count)

def check_list_loop : Nat → Nat → List Nat → Bool
  | cur_n, stop, [] => cur_n == stop
  | cur_n, stop, v :: vs =>
    let count := if cur_n + 1000 > stop then stop - cur_n else 1000
    let (ok, next_n) := check_huge cur_n v count
    if ok then check_list_loop next_n stop vs else false

def check_list (n stop : Nat) (l : List Nat) : Bool :=
  check_list_loop n stop l
