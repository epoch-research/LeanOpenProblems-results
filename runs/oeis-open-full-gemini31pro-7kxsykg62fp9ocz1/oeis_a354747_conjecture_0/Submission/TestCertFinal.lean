import FormalConjectures.Util.ProblemImports
import Submission.TestFastPow
import Submission.TestPow100943
import Submission.TestCertDecideMain

set_option exponentiation.threshold 1000000
set_option maxRecDepth 200000

namespace R

def my_M : ℕ := 2 * 100943 * 3^39101

theorem chain_M2_start_val_eq_pow : chain_M2_start_val = pow alpha 100943 := by
  dsimp [chain_M2_start_val]
  rw [pow_100943_eq]

theorem chain_M3_start_val_eq_pow : chain_M3_start_val = pow alpha (2 * 100943) := by
  dsimp [chain_M3_start_val]
  rw [pow_100943_eq, ←pow_add]

theorem chain_Mp_start_val_eq_pow : chain_Mp_start_val = pow alpha 2 := by
  dsimp [chain_Mp_start_val]
  rfl

theorem chain_M_start_val_eq_pow : chain_M_start_val = pow alpha (2 * 100943) := by
  dsimp [chain_M_start_val]
  rw [chain_M3_start_val_eq_pow]

theorem val_M2_eq_pow : chain_M2_final = pow alpha (my_M / 2) := by
  have h_div : my_M / 2 = 100943 * 3^39101 := rfl
  rw [h_div]
  rw [←chain_M2_final_eq]
  rw [chain_M2_start_val_eq_pow]
  rw [cube_pow_eq_pow, ←pow_mul]

theorem val_M3_eq_pow : chain_M3_final = pow alpha (my_M / 3) := by
  have h_div : my_M / 3 = 2 * 100943 * 3^39100 := by rfl
  rw [h_div]
  rw [←chain_M3_final_eq]
  rw [chain_M3_start_val_eq_pow]
  rw [cube_pow_eq_pow, ←pow_mul]

theorem val_Mp_eq_pow : chain_Mp_final = pow alpha (my_M / 100943) := by
  have h_div : my_M / 100943 = 2 * 3^39101 := by rfl
  rw [h_div]
  rw [←chain_Mp_final_eq]
  rw [chain_Mp_start_val_eq_pow]
  rw [cube_pow_eq_pow, ←pow_mul]

theorem val_M_eq_pow : chain_M_final = pow alpha my_M := by
  have h_div : my_M = 2 * 100943 * 3^39101 := rfl
  rw [h_div]
  rw [←chain_M_final_eq]
  rw [chain_M_start_val_eq_pow]
  rw [cube_pow_eq_pow, ←pow_mul]

end R

