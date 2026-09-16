import Mathlib
def a_comp (n : ℕ) : ℕ :=
  let divs := n.divisors
  let tau_n := divs.card
  let sum_d := divs.sum (fun d => d * (Nat.divisors d).card)
  sum_d - n * tau_n
def check_range (start stop : ℕ) : Bool :=
  (List.range (stop - start)).all (fun i => let n := start + i; if 0 < n ∧ n ≠ 21 then a_comp n ≠ n else true)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_1 : check_range 1 400 = true := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_2 : check_range 400 800 = true := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_3 : check_range 800 1200 = true := by decide
