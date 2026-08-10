import FormalConjectures.Util.ProblemImports

open Nat Finset

def is_square_kernel (m : ℕ) : Bool :=
  (List.range (m + 1)).any (fun r => r * r == m)

def a_kernel (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if is_square_kernel m then 1 else 0

theorem test_decide : a_kernel 9 > 0 := by
  decide
