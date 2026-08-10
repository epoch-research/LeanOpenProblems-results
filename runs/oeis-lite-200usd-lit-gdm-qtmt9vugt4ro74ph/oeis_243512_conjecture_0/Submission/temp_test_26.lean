import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

theorem test_sigma_172 : sigma 1 172 = 308 := by
  have h_dec : 172 = 4 * 43 := by rfl
  have h_cop : Coprime 4 43 := by decide
  rw [h_dec]
  rw [sigma_one_mul_coprime 4 43 h_cop]
  have h4 : sigma 1 4 = 7 := by rfl
  have h43 : sigma 1 43 = 44 := by rfl
  rw [h4, h43]

theorem test_sigma_522 : sigma 1 522 = 1170 := by
  have h_dec : 522 = 2 * (9 * 29) := by rfl
  have h_cop1 : Coprime 2 (9 * 29) := by decide
  have h_cop2 : Coprime 9 29 := by decide
  rw [h_dec]
  rw [sigma_one_mul_coprime 2 (9 * 29) h_cop1]
  rw [sigma_one_mul_coprime 9 29 h_cop2]
  have h2 : sigma 1 2 = 3 := by rfl
  have h9 : sigma 1 9 = 13 := by rfl
  have h29 : sigma 1 29 = 30 := by rfl
  rw [h2, h9, h29]

theorem test_sigma_81 : sigma 1 81 = 121 := by
  rfl

def A243473_val_test (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem test_34 : A243473_val_test 172 = 34 := by
  unfold A243473_val_test
  have h_ne : ¬ 172 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 172 = 308 := test_sigma_172
  rw [h_sig]
  norm_num
  rfl

theorem test_36 : A243473_val_test 522 = 36 := by
  unfold A243473_val_test
  have h_ne : ¬ 522 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 522 = 1170 := test_sigma_522
  rw [h_sig]
  norm_num
  rfl

theorem test_40 : A243473_val_test 81 = 40 := by
  unfold A243473_val_test
  have h_ne : ¬ 81 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 81 = 121 := test_sigma_81
  rw [h_sig]
  norm_num
  rfl
