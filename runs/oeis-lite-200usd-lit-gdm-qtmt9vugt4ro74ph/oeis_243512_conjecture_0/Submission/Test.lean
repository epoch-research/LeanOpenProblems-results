import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

def A243473_val_test (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

noncomputable def a_test (n : ℕ) : ℕ :=
  sInf {i : ℕ | 0 < i ∧ A243473_val_test i = n}

theorem a_two_exists : ∃ i, 0 < i ∧ A243473_val_test i = 2 := by
  use 120
  refine ⟨by decide, ?_⟩
  unfold A243473_val_test
  have h1 : ¬ 120 = 0 := by decide
  rw [if_neg h1]
  decide



















#check Nat.forall_exists_prime_gt_and_modEq