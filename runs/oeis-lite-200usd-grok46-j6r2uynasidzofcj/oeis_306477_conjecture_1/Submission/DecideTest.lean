import FormalConjectures.Util.ProblemImports

open Nat Finset

def binom2468 (w x y z : ℕ) : ℕ :=
  (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8

def hasRep (n : ℕ) : Bool :=
  (range (n + 1)).any fun w =>
    (range (n + 1)).any fun x =>
      (range (n + 1)).any fun y =>
        (range (n + 1)).any fun z =>
          binom2468 w x y z == n

-- smarter search
def isTri (m : ℕ) : Bool :=
  let t := 8 * m + 1
  let s := Nat.sqrt t
  decide (s * s = t ∧ 3 ≤ s ∧ s % 2 = 1)

def hasRep2 (n : ℕ) : Bool :=
  (range (n + 1)).any fun z =>
    let Sz := (z + 7).choose 8
    Sz ≤ n &&
    (range (n + 1)).any fun y =>
      let Ry := (y + 5).choose 6
      Ry ≤ n - Sz &&
      (range (n + 1)).any fun x =>
        let Qx := (x + 3).choose 4
        Qx ≤ n - Sz - Ry &&
        isTri (n - Sz - Ry - Qx)

set_option maxHeartbeats 4000000

theorem test10 : ∀ n ∈ Icc 1 10, hasRep2 n = true := by decide
