import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000000
set_option maxHeartbeats 1000000000

open Nat

def reverse_fast_loop : ℕ → ℕ → ℕ → ℕ
  | 0, acc, _ => acc
  | fuel + 1, acc, n =>
    if n = 0 then acc
    else reverse_fast_loop fuel (acc * 10 + n % 10) (n / 10)

def reverse_fast (n : ℕ) : ℕ :=
  reverse_fast_loop n 0 n

-- Let's write a loop to check if any k < bound satisfies the property.
def check_loop (N : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, k =>
    if k = 0 then false
    else
      if (reverse_fast (k * N)) % N == 0 then true
      else check_loop N fuel (k - 1)

-- Let's see how fast Lean's kernel can evaluate this for N = 81 and bound = 10000.
-- Let's try 10,000 first.
theorem check_10k : check_loop 81 10000 10000 = false := by decide
