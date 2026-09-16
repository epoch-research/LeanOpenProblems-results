import Mathlib

def a_fast_prim (n : UInt64) : Bool :=
  let N := 6 * n + 1
  let max_z := (N / 7).toFloat.sqrt.toUInt64
  let rec loop_z (z : UInt64) (count : UInt64) : Bool :=
    if z > max_z then false
    else
      let rem1 := N - 7 * z * z
      let max_y := (rem1 / 3).toFloat.sqrt.toUInt64
      let rec loop_y (y : UInt64) (cnt : UInt64) : UInt64 :=
        if y > max_y then cnt
        else
          let rem2 := rem1 - 3 * y * y
          let new_cnt :=
            if rem1 > 3 * y * y then
              let x := rem2.toFloat.sqrt.toUInt64
              if x * x == rem2 then cnt + 1 else cnt
            else cnt
          if new_cnt > 1 then new_cnt
          else loop_y (y + 1) new_cnt
      let c := loop_y 0 count
      if c > 1 then true else loop_z (z + 1) c
  loop_z 0 0

def check_all_prim (start_n end_n : UInt64) : Bool :=
  let rec go (n : UInt64) : Bool :=
    if n ≥ end_n then
      a_fast_prim n
    else
      if a_fast_prim n then
        go (n + 1)
      else false
  go start_n

theorem test : check_all_prim 287 100000 = true := by native_decide
