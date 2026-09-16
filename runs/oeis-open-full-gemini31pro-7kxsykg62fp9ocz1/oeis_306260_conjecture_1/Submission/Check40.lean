import FormalConjectures.Util.ProblemImports

open Finset Nat

def A306260_check (n : ℕ) : ℕ :=
  let P₁ (w : ℕ) : ℕ := w * (4 * w + 1)
  let P₂ (x : ℕ) : ℕ := x * (4 * x - 1)
  let P₃ (y : ℕ) : ℕ := y * (4 * y - 2)
  let P₄ (z : ℕ) : ℕ := z * (4 * z - 3)
  let B : ℕ := n.succ
  let R := range B 
  R.sum fun w =>
    R.sum fun x =>
      R.sum fun y =>
        R.sum fun z =>
          if P₁ w + P₂ x + P₃ y + P₄ z = n then 1 else 0

#eval (List.range 40).filter (fun n => A306260_check n == 1)
