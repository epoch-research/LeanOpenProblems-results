import FormalConjectures.Util.ProblemImports
open Nat
-- reduced-range version (equal to A273110 since valid reps have vars ≤ √n ≤ d)
def Afast (n : ℕ) : ℕ :=
  let d : ℕ := n.sqrt
  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2
    if x^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ (IsSquare E)
    then 1 else 0
def Mset : List ℕ := [1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671]
def rhs (n : ℕ) : Bool := (List.range 30).any (fun k => Mset.any (fun m => n = 4^k * m))
def Pholds (n : ℕ) : Bool :=
  let a := Afast n
  ((n == 0) || (a != 0)) && ((a == 1) == (rhs n))
#eval ((List.range 800).filter (fun n => ! Pholds n))   -- expect [] if no small counterexample
