import Mathlib.Data.Nat.Basic

set_option maxRecDepth 100000

open Nat

def sqrt_loop (n : ℕ) (k : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => k
  | f + 1 =>
    if (k + 1) * (k + 1) > n then k
    else sqrt_loop n (k + 1) f

def sqrt_fast (n : ℕ) : ℕ :=
  sqrt_loop n 0 n

def min_fac_loop (n : ℕ) (d : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | f + 1 =>
    if d * d > n then n
    else if n % d = 0 then d
    else min_fac_loop n (d + 2) f

def min_fac_fast (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else if n % 2 = 0 then 2
  else min_fac_loop n 3 (sqrt_fast n / 2 + 1)

def get_prime_factors_loop (n : ℕ) (fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if n ≤ 1 then []
    else
      let p := min_fac_fast n
      p :: get_prime_factors_loop (n / p) f

def get_prime_factors_fast (n : ℕ) : List ℕ :=
  get_prime_factors_loop n 25

def totient_from_factors : List ℕ → ℕ
  | [] => 1
  | [p] => p - 1
  | p1 :: p2 :: ps =>
    if p1 = p2 then
      p1 * totient_from_factors (p2 :: ps)
    else
      (p1 - 1) * totient_from_factors (p2 :: ps)

def totient_factor (n : ℕ) : ℕ :=
  if n = 0 then 0
  else totient_from_factors (get_prime_factors_fast n)

example : totient_factor 1999999 = 1854720 := by decide
