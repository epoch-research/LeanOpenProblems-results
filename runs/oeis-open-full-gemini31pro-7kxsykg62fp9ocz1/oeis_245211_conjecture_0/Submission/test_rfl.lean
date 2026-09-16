import Mathlib
def a_comp (n : ℕ) : ℕ :=
  let divs := n.divisors
  let tau_n := divs.card
  let sum_d := divs.sum (fun d => d * (Nat.divisors d).card)
  sum_d - n * tau_n
lemma a_22 : a_comp 22 = 27 := by decide
