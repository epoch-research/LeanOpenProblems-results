import Submission.Spec
open Nat List Finset

set_option maxHeartbeats 0

def get_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0)

def a_comp (n : ℕ) : ℕ :=
  let divisors_list : List ℕ := get_divisors n
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum
  if s = 0 then 0 else n ^ 2 / s

def check_loop (k : ℕ) (n : ℕ) : Bool :=
  if n < 2 then true
  else if a_comp n == k then false
  else check_loop k (n - 1)

def check_all_14_full : Bool :=
  a_comp 6678671 == 14 && check_loop 14 6678670

#eval check_all_14_full
