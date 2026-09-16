import Mathlib

def linear_sqrt (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc x =>
    if x * x <= n then x else acc
  ) 0

def a_fold (n : Nat) : Nat :=
  let N := 6 * n + 1
  let max_z := linear_sqrt (N / 7)
  (List.range (max_z + 1)).foldl (fun acc z =>
    let rem1 := N - 7 * z * z
    let max_y := linear_sqrt (rem1 / 3)
    acc + (List.range (max_y + 1)).foldl (fun acc_y y =>
      let rem2 := rem1 - 3 * y * y
      if rem2 > 0 then
        let x := linear_sqrt rem2
        if x * x == rem2 then acc_y + 1 else acc_y
      else acc_y
    ) 0
  ) 0

set_option maxRecDepth 2000000
theorem test_fold : a_fold 287 = 14 := by decide
