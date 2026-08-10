import Mathlib
open Nat Finset
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))))
#eval (List.range 60).map (fun n => (n, A306477 n))
#eval ((List.range 200).filter (fun n => n > 0 && A306477 n == 0))
