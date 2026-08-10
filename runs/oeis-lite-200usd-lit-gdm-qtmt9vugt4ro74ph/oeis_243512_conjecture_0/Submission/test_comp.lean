import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem test_10 : A243473_val 120 = 2 := by
  unfold A243473_val
  have h1 : ¬ 120 = 0 := by decide
  rw [if_neg h1]
  have h_sig : sigma 1 120 = 360 := by rfl
  rw [h_sig]
  norm_num
  rfl
