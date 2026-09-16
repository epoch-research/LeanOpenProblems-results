import Submission.Spec
open Nat Finset

def a_comp (n : ℕ) : ℕ :=
  let omega (m : ℕ) : ℕ :=
    if m ≤ 1 then 0
    else (Nat.factorization m).sum (fun _ k => k)
  let is_semiprime (m : ℕ) : Bool := omega m == 2
  let k_max := Nat.sqrt n
  let k_candidates := List.range (k_max + 1)
  match k_candidates.find? (fun k => is_semiprime (n - k * k)) with
  | some k => k * k
  | none   => 2

#eval a_comp 16
