import FormalConjectures.Util.ProblemImports

open Nat

def nextPrimeFuel : ℕ → ℕ → ℕ
  | 0, s => s
  | fuel + 1, s => if s.Prime then s else nextPrimeFuel fuel (s + 1)

def nextPrimeAfter (s : ℕ) : ℕ := nextPrimeFuel (s + 1) (s + 1)

def intervalHasPrimeTR : ℕ → ℕ → Bool
  | _, 0 => false
  | lo, len+1 => if lo.Prime then true else intervalHasPrimeTR (lo+1) len

def holdsSmart (n : ℕ) : Bool :=
  let s := Nat.sqrt n
  let q := nextPrimeAfter s
  intervalHasPrimeTR (q * q - n) (2 * q + 1)

def allHoldsRange (lo hi : ℕ) : Bool :=
  if lo > hi then true
  else if lo = hi then holdsSmart lo
  else
    let mid := (lo + hi) / 2
    allHoldsRange lo mid && allHoldsRange (mid + 1) hi
termination_by hi + 1 - lo

lemma test : allHoldsRange 2001 10000000 = true := by
  native_decide
