import Submission.Spec
open Nat List Finset

def a_comp (n : ℕ) : ℕ :=
  let divisors_list : List ℕ := (Nat.divisors n).toList.mergeSort (· ≤ ·)
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum
  if s = 0 then 0 else n ^ 2 / s
