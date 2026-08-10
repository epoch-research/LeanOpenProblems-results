import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def remove_p_fuel (p : ℕ) : ℕ → ℕ → ℕ
  | 0, t => t
  | fuel + 1, t =>
    if t % p = 0 then remove_p_fuel p fuel (t / p) else t

def totient_loop_fuel : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, temp, p, acc =>
    if p * p > temp then
      if temp > 1 then acc - acc / temp else acc
    else if temp % p = 0 then
      let acc' := acc - acc / p
      let temp' := remove_p_fuel p temp temp
      let next_p := if p = 2 then 3 else p + 2
      totient_loop_fuel fuel temp' next_p acc'
    else
      let next_p := if p = 2 then 3 else p + 2
      totient_loop_fuel fuel temp next_p acc

def totient_fast (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_loop_fuel n n 2 n

theorem test_speed : totient_fast 1999993 = 1999992 := by decide
