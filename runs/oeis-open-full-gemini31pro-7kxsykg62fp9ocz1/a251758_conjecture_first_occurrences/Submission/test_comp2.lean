import Submission.Spec
open Nat List Finset

def get_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0)

def a_comp (n : ℕ) : ℕ :=
  let divisors_list : List ℕ := get_divisors n
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum
  if s = 0 then 0 else n ^ 2 / s

theorem a_eq_a_comp (n : ℕ) : a n = a_comp n := sorry
