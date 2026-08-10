import FormalConjectures.Util.ProblemImports
open Nat Finset

def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w => R.sum (fun x => R.sum (fun y => R.sum (fun z =>
    if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))))

example : ∀ n : ℕ, n > 0 → A306477 n > 0 := by
  classical
  native_decide
