import Mathlib

def a_comp (n : ℕ) : ℕ :=
  let divs := Nat.divisors n
  let tau_n := divs.card
  let sum_d := divs.sum (fun d => d * (Nat.divisors d).card)
  sum_d - n * tau_n

def check_range (start stop : ℕ) : Bool :=
  (List.range (stop - start)).all (fun i =>
    let n := start + i
    if 0 < n ∧ n ≠ 21 then a_comp n ≠ n else true)

#eval check_range 1 50000
