import Mathlib

def a_fast_aux : ℕ → ℕ × ℕ
| 0 => (0, 1)
| n + 1 =>
  let (prev2, prev) := a_fast_aux n
  let res := if prev.Prime ∧ prev > 2 then prev - prev2 else prev + prev2
  (prev, res)

def a_fast (n : ℕ) : ℕ := (a_fast_aux n).1

def find_counter : ℕ → Option ℕ
| 0 => none
| n + 1 =>
  let (prev2, prev) := a_fast_aux n
  let res := if prev.Prime ∧ prev > 2 then prev - prev2 else prev + prev2
  if res < prev ∧ res.Prime ∧ res > 2 then
    some n
  else
    find_counter n

#eval find_counter 1000
