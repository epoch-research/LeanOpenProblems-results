import Mathlib
def a_comp (n : ℕ) : ℕ :=
  let divs := n.divisors
  let tau_n := divs.card
  let sum_d := divs.sum (fun d => d * (Nat.divisors d).card)
  sum_d - n * tau_n
def check_range (m : ℕ) : Bool :=
  (List.range m).all (fun n => if 0 < n ∧ n ≠ 21 then a_comp n ≠ n else true)
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_700 : check_range 700 = true := by decide
