import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

def A243473_val_test (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem test_64 : A243473_val_test 332 = 64 := by
  unfold A243473_val_test
  have h_ne : ¬ 332 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 332 = 588 := by
    have h_dec : 332 = 4 * 83 := by rfl
    have h_cop : Coprime 4 83 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 4 83 h_cop]
    have h4 : sigma 1 4 = 7 := by rfl
    have h83 : sigma 1 83 = 84 := by rfl
    rw [h4, h83]
  rw [h_sig]
  norm_num
  rfl

theorem test_66 : A243473_val_test 108000 = 66 := by
  unfold A243473_val_test
  have h_ne : ¬ 108000 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 108000 = 393120 := by
    have h_dec : 108000 = 32 * (27 * 125) := by rfl
    have h_cop1 : Coprime 32 (27 * 125) := by decide
    have h_cop2 : Coprime 27 125 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 32 (27 * 125) h_cop1]
    rw [sigma_one_mul_coprime 27 125 h_cop2]
    have h32 : sigma 1 32 = 63 := by rfl
    have h27 : sigma 1 27 = 40 := by rfl
    have h125 : sigma 1 125 = 156 := by rfl
    rw [h32, h27, h125]
  rw [h_sig]
  norm_num
  rfl

theorem test_78 : A243473_val_test 2047488 = 78 := by
  unfold A243473_val_test
  have h_ne : ¬ 2047488 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 2047488 = 5761536 := by
    have h_dec : 2047488 = 512 * (3 * (31 * 43)) := by rfl
    have h_cop1 : Coprime 512 (3 * (31 * 43)) := by decide
    have h_cop2 : Coprime 3 (31 * 43) := by decide
    have h_cop3 : Coprime 31 43 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 512 (3 * (31 * 43)) h_cop1]
    rw [sigma_one_mul_coprime 3 (31 * 43) h_cop2]
    rw [sigma_one_mul_coprime 31 43 h_cop3]
    have h512 : sigma 1 512 = 1023 := by rfl
    have h3 : sigma 1 3 = 4 := by rfl
    have h31 : sigma 1 31 = 32 := by rfl
    have h43 : sigma 1 43 = 44 := by rfl
    rw [h512, h3, h31, h43]
  rw [h_sig]
  norm_num
  rfl

theorem test_82 : A243473_val_test 260 = 82 := by
  unfold A243473_val_test
  have h_ne : ¬ 260 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 260 = 588 := by
    have h_dec : 260 = 4 * (5 * 13) := by rfl
    have h_cop1 : Coprime 4 (5 * 13) := by decide
    have h_cop2 : Coprime 5 13 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 4 (5 * 13) h_cop1]
    rw [sigma_one_mul_coprime 5 13 h_cop2]
    have h4 : sigma 1 4 = 7 := by rfl
    have h5 : sigma 1 5 = 6 := by rfl
    have h13 : sigma 1 13 = 14 := by rfl
    rw [h4, h5, h13]
  rw [h_sig]
  norm_num
  rfl

theorem test_86 : A243473_val_test 2680 = 86 := by
  unfold A243473_val_test
  have h_ne : ¬ 2680 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 2680 = 6120 := by
    have h_dec : 2680 = 8 * (5 * 67) := by rfl
    have h_cop1 : Coprime 8 (5 * 67) := by decide
    have h_cop2 : Coprime 5 67 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 8 (5 * 67) h_cop1]
    rw [sigma_one_mul_coprime 5 67 h_cop2]
    have h8 : sigma 1 8 = 15 := by rfl
    have h5 : sigma 1 5 = 6 := by rfl
    have h67 : sigma 1 67 = 68 := by rfl
    rw [h8, h5, h67]
  rw [h_sig]
  norm_num
  rfl

theorem test_93 : A243473_val_test 1027 = 93 := by
  unfold A243473_val_test
  have h_ne : ¬ 1027 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 1027 = 1120 := by
    have h_dec : 1027 = 13 * 79 := by rfl
    have h_cop : Coprime 13 79 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 13 79 h_cop]
    have h13 : sigma 1 13 = 14 := by rfl
    have h79 : sigma 1 79 = 80 := by rfl
    rw [h13, h79]
  rw [h_sig]
  norm_num
  rfl

theorem test_94 : A243473_val_test 1464 = 94 := by
  unfold A243473_val_test
  have h_ne : ¬ 1464 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 1464 = 3720 := by
    have h_dec : 1464 = 8 * (3 * 61) := by rfl
    have h_cop1 : Coprime 8 (3 * 61) := by decide
    have h_cop2 : Coprime 3 61 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 8 (3 * 61) h_cop1]
    rw [sigma_one_mul_coprime 3 61 h_cop2]
    have h8 : sigma 1 8 = 15 := by rfl
    have h3 : sigma 1 3 = 4 := by rfl
    have h61 : sigma 1 61 = 62 := by rfl
    rw [h8, h3, h61]
  rw [h_sig]
  norm_num
  rfl

theorem test_96 : A243473_val_test 2832 = 96 := by
  unfold A243473_val_test
  have h_ne : ¬ 2832 = 0 := by decide
  rw [if_neg h_ne]
  have h_sig : sigma 1 2832 = 7440 := by
    have h_dec : 2832 = 16 * (3 * 59) := by rfl
    have h_cop1 : Coprime 16 (3 * 59) := by decide
    have h_cop2 : Coprime 3 59 := by decide
    rw [h_dec]
    rw [sigma_one_mul_coprime 16 (3 * 59) h_cop1]
    rw [sigma_one_mul_coprime 3 59 h_cop2]
    have h16 : sigma 1 16 = 31 := by rfl
    have h3 : sigma 1 3 = 4 := by rfl
    have h59 : sigma 1 59 = 60 := by rfl
    rw [h16, h3, h59]
  rw [h_sig]
  norm_num
  rfl
