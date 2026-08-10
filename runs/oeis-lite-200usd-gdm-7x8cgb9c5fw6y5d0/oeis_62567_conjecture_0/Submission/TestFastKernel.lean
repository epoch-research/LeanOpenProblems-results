import FormalConjectures.Util.ProblemImports

open Nat

-- We want a fast, tail-recursive digit extraction and reversal.
-- We can do it by maintaining the reversed number directly during division.
def reverse_fast_loop (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | n => reverse_fast_loop (acc * 10 + n % 10) (n / 10)

def reverse_fast (n : ℕ) : ℕ :=
  reverse_fast_loop 0 n

-- Let's check if reverse_fast is indeed reverse_nat
theorem reverse_fast_eq_reverse_nat (n : ℕ) : reverse_fast n = ofDigits 10 (digits 10 n).reverse := by
  sorry -- we will prove this later if needed

-- Let's write a loop to check if any k < bound satisfies the property.
def check_loop (N : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, k =>
    if k = 0 then false
    else
      if (reverse_fast (k * N)) % N == 0 then true
      else check_loop N fuel (k - 1)

-- Let's see how fast Lean's kernel can evaluate this for N = 81 and bound = 100000.
-- We start the check at 100000.
theorem check_100k : check_loop 81 100000 100000 = false := by decide
