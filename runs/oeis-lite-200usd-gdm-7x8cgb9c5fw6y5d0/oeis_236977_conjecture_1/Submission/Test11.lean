import FormalConjectures.Util.ProblemImports

open Nat

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
      totient_loop_fuel fuel temp' (p + 1) acc'
    else
      totient_loop_fuel fuel temp (p + 1) acc

def totient_fast (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_loop_fuel n n 2 n

theorem test_decide : totient_fast 100000 = 40000 := by
  decide
