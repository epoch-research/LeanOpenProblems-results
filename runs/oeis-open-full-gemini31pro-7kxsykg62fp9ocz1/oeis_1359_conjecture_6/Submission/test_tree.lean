import Mathlib
open Nat

def isPrimeFast : ℕ → Bool
| 0 => false
| 1 => false
| n =>
  let rec check (d : ℕ) (fuel : ℕ) : Bool :=
    match fuel with
    | 0 => true
    | f + 1 =>
      if d * d > n then true
      else if n % d == 0 then false
      else check (d + 1) f
  check 2 n

def countPrimesTree (low high : ℕ) : ℕ :=
  if h : high <= low + 1 then
    if high = low + 1 then
      if isPrimeFast low then 1 else 0
    else 0
  else
    have h1 : low + 1 < high := by omega
    let mid := (low + high) / 2
    have t1 : mid - low < high - low := by omega
    have t2 : high - mid < high - low := by omega
    countPrimesTree low mid + countPrimesTree mid high
termination_by high - low

lemma cp_7842 : countPrimesTree 0 7842 = 991 := by decide
