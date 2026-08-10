import FormalConjectures.Util.ProblemImports

open Nat

def reverse_fast_loop : ℕ → ℕ → ℕ → ℕ
  | 0, acc, _ => acc
  | fuel + 1, acc, n =>
    if n = 0 then acc
    else reverse_fast_loop fuel (acc * 10 + n % 10) (n / 10)

def reverse_fast (n : ℕ) : ℕ :=
  reverse_fast_loop n 0 n

def check_tree (N : ℕ) (start : ℕ) (len : ℕ) : Bool :=
  if len ≤ 1 then
    if len = 1 then (reverse_fast (start * N)) % N == 0
    else false
  else
    let half := len / 2
    check_tree N start half || check_tree N (start + half) (len - half)

-- Let's see if we can evaluate check_tree for N = 81 and len = 100000.
theorem check_100k : check_tree 81 1 100000 = false := by decide
