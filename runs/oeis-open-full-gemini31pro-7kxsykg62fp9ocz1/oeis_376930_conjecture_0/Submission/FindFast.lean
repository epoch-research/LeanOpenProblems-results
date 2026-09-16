import Mathlib

def a_fast_aux : ℕ → ℕ × ℕ
| 0 => (0, 1)
| n + 1 =>
  let (prev2, prev) := a_fast_aux n
  let res := if prev.Prime ∧ prev > 2 then prev - prev2 else prev + prev2
  (prev, res)

def find_counter_loop : ℕ → ℕ → ℕ × ℕ → Option ℕ
| 0, _, _ => none
| k + 1, n, (prev2, prev) =>
  let res := if prev.Prime ∧ prev > 2 then prev - prev2 else prev + prev2
  if res.Prime ∧ res > 2 ∧ res < prev then
    some n
  else
    find_counter_loop k (n + 1) (prev, res)

#eval find_counter_loop 1000 1 (0, 1)
