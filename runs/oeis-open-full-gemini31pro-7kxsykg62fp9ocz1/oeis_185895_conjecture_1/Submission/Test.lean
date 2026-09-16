import Submission.Spec
open Polynomial Nat Finset

#eval (List.range 15).map (fun n => A185895 n)

def check_conj (n : ℕ) : Bool :=
  let prod_neg := (A185895 n * A185895 (n - 1) < 0)
  let is_tri := (∃ k, k * (k + 1) / 2 = n)
  -- Wait, exist is not decidable directly, let's just write a bool check
  let is_tri_bool := (List.range (n + 1)).any (fun k => k * (k + 1) / 2 == n)
  prod_neg == is_tri_bool

#eval (List.range 15).drop 1 |>.map check_conj
