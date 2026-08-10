partial def has_partition (M N limit : Nat) : Bool :=
  let rec dfs (depth current_sum last_val : Nat) : Bool :=
    if depth = M then
      current_sum = N
    else
      let rem_len := M - depth
      let max_val1 := (N - current_sum) / rem_len
      let max_val2 := if current_sum < limit then current_sum + 1 else N
      let high := Nat.min max_val1 max_val2
      if high < last_val then false
      else
        let rec loop (val : Nat) : Bool :=
          if val > high then false
          else dfs (depth + 1) (current_sum + val) val || loop (val + 1)
        loop last_val
  dfs 0 0 1

#eval has_partition 19 1079 1023





