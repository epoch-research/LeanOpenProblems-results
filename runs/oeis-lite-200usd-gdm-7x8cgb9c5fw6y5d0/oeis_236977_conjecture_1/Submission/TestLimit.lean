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

def sqrt_binary_loop (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, high => high
  | fuel + 1, low, high =>
    if low > high then high
    else
      let mid := (low + high) / 2
      let sq := mid * mid
      if sq = m then mid
      else if sq > m then
        if mid == 0 then low
        else sqrt_binary_loop m fuel low (mid - 1)
      else
        sqrt_binary_loop m fuel (mid + 1) high

def sqrt_fast (m : Nat) : Nat :=
  sqrt_binary_loop m 40 0 m

def is_square_fast (m : Nat) : Bool :=
  let r := sqrt_fast m
  r * r == m

def check_all_loop : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then
      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true
      else
        let k := 1
        is_square_fast (totient_fast k * totient_fast (L - k))
    else
      let mid := (L + R) / 2
      check_all_loop fuel L mid && check_all_loop fuel (mid + 1) R

theorem test_decide : check_all_loop 25 9 10000 = true := by decide
