import FormalConjectures.Util.ProblemImports

open Nat

def holdsDec : ℕ → Bool := fun n =>
  let rec go : ℕ → Bool
    | 0 => false
    | p + 1 =>
        (p.Prime && (Nat.sqrt (n + p)).Prime) || go p
  go n

def allHold (N : ℕ) : Bool :=
  let rec go : ℕ → Bool
    | 0 => true
    | k + 1 =>
        (k ≤ 2 || holdsDec k) && go k
  go (N + 1)

#eval allHold 200

theorem test200 : allHold 200 = true := by native_decide
