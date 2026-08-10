import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

def A243473_val_test (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem a_zero_exists : ∃ i, 0 < i ∧ A243473_val_test i = 0 := by
  use 1
  refine ⟨by decide, ?_⟩
  unfold A243473_val_test
  have h1 : ¬ 1 = 0 := by decide
  rw [if_neg h1]
  simp [sigma_one]

theorem a_one_exists : ∃ i, 0 < i ∧ A243473_val_test i = 1 := by
  use 2
  refine ⟨by decide, ?_⟩
  unfold A243473_val_test
  have h1 : ¬ 2 = 0 := by decide
  rw [if_neg h1]
  simp [sigma_one]
  rfl

theorem a_two_exists : ∃ i, 0 < i ∧ A243473_val_test i = 2 := by
  use 120
  refine ⟨by decide, ?_⟩
  unfold A243473_val_test
  have h1 : ¬ 120 = 0 := by decide
  rw [if_neg h1]
  decide









