import Mathlib
def a_comp (n : ℕ) : ℕ := let divs := n.divisors; let tau_n := divs.card; divs.sum (fun d => d * (Nat.divisors d).card) - n * tau_n
def check_range (start stop : ℕ) : Bool := (List.range (stop - start)).all (fun i => let n := start + i; if 0 < n ∧ n ≠ 21 then a_comp n ≠ n else true)
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_0 : check_range 0 500 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_1 : check_range 500 1000 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_2 : check_range 1000 1500 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_3 : check_range 1500 2000 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_4 : check_range 2000 2500 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_5 : check_range 2500 3000 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_6 : check_range 3000 3500 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_7 : check_range 3500 4000 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_8 : check_range 4000 4500 = true := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
lemma check_9 : check_range 4500 5000 = true := by decide
