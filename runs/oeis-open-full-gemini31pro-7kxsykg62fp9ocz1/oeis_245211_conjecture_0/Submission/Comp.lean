import Mathlib
import Submission.Spec

open Nat Finset

def a_comp (n : ℕ) : ℕ :=
  let divs := n.divisors
  let full_sum := divs.sum (fun d => d * d.divisors.card)
  let self_term := n * n.divisors.card
  full_sum - self_term

lemma a_eq_a_comp (n : ℕ) : a n = a_comp n := rfl

lemma a_21 : a 21 = 21 := by
  rw [a_eq_a_comp]
  rfl
