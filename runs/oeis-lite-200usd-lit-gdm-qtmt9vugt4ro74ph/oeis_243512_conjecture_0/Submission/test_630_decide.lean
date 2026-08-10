import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem test_630 : A243473_val 40052517120 = 630 := by
  unfold A243473_val
  have h_ne : ¬ 40052517120 = 0 := by decide
  rw [if_neg h_ne]
  decide
