import Submission.Spec
import Mathlib

def a_comp (n : ℕ) : ℕ :=
  let divisors_list : List ℕ := (Nat.divisors n).sort (· ≤ ·)
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum
  if s = 0 then 0
  else n ^ 2 / s

theorem a_eq_a_comp (n : ℕ) : a n = a_comp n := rfl

theorem test : a 15 = 2 := by
  rw [a_eq_a_comp]
  decide
