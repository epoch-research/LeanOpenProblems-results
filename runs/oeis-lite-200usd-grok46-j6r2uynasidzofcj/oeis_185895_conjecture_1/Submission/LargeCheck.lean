import FormalConjectures.Util.ProblemImports

open Nat

def midShift (k : ℕ) : ℕ :=
  max (5 * k.sqrt) ((k * (3 * Nat.log 2 k + 8)).sqrt)

def prodRange (start len : ℕ) : ℕ :=
  (List.range len).foldl (fun acc i => acc * (start + i)) 1

def checkLargeL (k : ℕ) : Bool :=
  let s := midShift k
  let j := k - s + 1
  let a := s - 2
  let b := s - 13
  decide (4 * j * (13).factorial * prodRange k b ≤ prodRange (j + 1) a)

def checkLargeL_upto (K0 : ℕ) : Bool :=
  (List.range (K0 - 80)).all fun i => checkLargeL (i + 81)

-- small sanity
example : checkLargeL 81 = true := by native_decide
example : checkLargeL 82 = true := by native_decide

-- batch
example : checkLargeL_upto 2000 = true := by native_decide
