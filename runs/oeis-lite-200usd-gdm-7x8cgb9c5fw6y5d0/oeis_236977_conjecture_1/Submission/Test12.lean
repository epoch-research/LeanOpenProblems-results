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

def is_square_kernel (m : ℕ) : Bool :=
  -- We can use a faster square check by doing Newton's method or binary search
  -- but since m is at most (totient k * totient (n-k)) <= n^2,
  -- actually totient k * totient (n-k) is at most n * n.
  -- But wait, we can just use the fact that sqrt_fast is easy to define.
  -- Let's define a fast sqrt:
  let r := (List.range (m + 1)).any (fun r => r * r == m)
  r

-- Wait, List.range (m+1) is O(m), which is O(n^2), too slow!
-- We can do a faster square check without List.range!
-- A tail-recursive square check:
def is_square_loop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, m, r =>
    if r * r > m then false
    else if r * r == m then true
    else is_square_loop fuel m (r + 1)

def is_square_fast (m : ℕ) : Bool :=
  -- m is at most n * n, so its square root is at most n.
  -- Thus fuel of n is plenty!
  is_square_loop (m + 1) m 0

-- Let's define a search for k
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
