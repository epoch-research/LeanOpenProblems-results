import Mathlib

def sigma_comp (n : ℕ) : ℕ := n.divisors.sum id

def a_comp (n : ℕ) : ℕ :=
  let divs := n.divisors
  let tau_n := divs.card
  let sum_d := divs.sum (fun d => d * (Nat.divisors d).card)
  sum_d - n * tau_n

def check_loop (start : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    let n := start + k
    if n % 2 == 0 then check_loop start k
    else if 2 * sigma_comp n > 3 * n + 1 then check_loop start k
    else if n = 21 then check_loop start k
    else if a_comp n = n then false
    else check_loop start k

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000000 in
lemma check_1000 : check_loop 1 1000 = true := by decide
