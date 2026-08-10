import FormalConjectures.Util.ProblemImports
open Nat Finset

def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)
  S.sum fun a =>
    S.sum fun b =>
      S.sum fun c =>
        S.sum fun d =>
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0

example : A352628 31 > 0 := by
  native_decide

example (n : ℕ) : A352628 n > 0 := by
  native_decide +revert
