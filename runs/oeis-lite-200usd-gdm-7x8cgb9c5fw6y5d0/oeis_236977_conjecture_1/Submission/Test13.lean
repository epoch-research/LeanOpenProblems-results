import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

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

def is_square_loop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, m, r =>
    if r * r > m then false
    else if r * r == m then true
    else is_square_loop fuel m (r + 1)

def is_square_fast (m : ℕ) : Bool :=
  is_square_loop (m + 1) m 0

def find_k_loop : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, n, k =>
    if k > (n - 1) / 2 then 0
    else
      let m := totient_fast k * totient_fast (n - k)
      if is_square_fast m then k
      else find_k_loop fuel n (k + 1)

def check_all_loop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, n, max_n =>
    if n > max_n then true
    else if find_k_loop n n 1 == 0 then false
    else check_all_loop fuel (n + 1) max_n

theorem test_decide : check_all_loop 1000 9 1000 = true := by
  decide
