import FormalConjectures.Util.ProblemImports

open Nat

def reverse_fast_loop : ℕ → ℕ → ℕ → ℕ
  | 0, acc, _ => acc
  | fuel + 1, acc, n =>
    if n = 0 then acc
    else reverse_fast_loop fuel (acc * 10 + n % 10) (n / 10)

def reverse_fast (n : ℕ) : ℕ :=
  reverse_fast_loop n 0 n

def check_tree_fuel (N : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, start, len =>
    if len ≤ 1 then
      if len = 1 then (reverse_fast (start * N)) % N == 0
      else false
    else
      let half := len / 2
      check_tree_fuel N fuel start half || check_tree_fuel N fuel (start + half) (len - half)

theorem check_10k : check_tree_fuel 81 20 1 10000 = false := by decide
