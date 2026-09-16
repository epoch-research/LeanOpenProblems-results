import Mathlib

set_option maxRecDepth 20000000
set_option maxHeartbeats 20000000

def isPrimeBool (n : ℕ) : Bool :=
  if n < 2 then false
  else
    (List.range n).all (fun d => d < 2 ∨ n % d ≠ 0)

def countPrimesBool (n : ℕ) : ℕ :=
  (List.range n).foldl (fun c k => if isPrimeBool k then c + 1 else c) 0

lemma count_is_990 : countPrimesBool 7841 = 990 := by decide
