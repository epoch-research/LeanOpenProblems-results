import FormalConjectures.Util.ProblemImports
import Submission.TestFastPow
namespace R
def pow_1 {n_p} (x : R n_p) := x
theorem pow_1_eq {n_p} (x : R n_p) : pow_1 x = pow x 1 := by simp [pow_1, pow]
def pow_2 {n_p} (x : R n_p) : R n_p := mul (pow_1 x) (pow_1 x)
def pow_3 {n_p} (x : R n_p) : R n_p := mul (pow_2 x) x
def pow_6 {n_p} (x : R n_p) : R n_p := mul (pow_3 x) (pow_3 x)
def pow_12 {n_p} (x : R n_p) : R n_p := mul (pow_6 x) (pow_6 x)
def pow_24 {n_p} (x : R n_p) : R n_p := mul (pow_12 x) (pow_12 x)
def pow_48 {n_p} (x : R n_p) : R n_p := mul (pow_24 x) (pow_24 x)
def pow_49 {n_p} (x : R n_p) : R n_p := mul (pow_48 x) x
def pow_98 {n_p} (x : R n_p) : R n_p := mul (pow_49 x) (pow_49 x)
def pow_196 {n_p} (x : R n_p) : R n_p := mul (pow_98 x) (pow_98 x)
def pow_197 {n_p} (x : R n_p) : R n_p := mul (pow_196 x) x
def pow_394 {n_p} (x : R n_p) : R n_p := mul (pow_197 x) (pow_197 x)
def pow_788 {n_p} (x : R n_p) : R n_p := mul (pow_394 x) (pow_394 x)
def pow_1576 {n_p} (x : R n_p) : R n_p := mul (pow_788 x) (pow_788 x)
def pow_1577 {n_p} (x : R n_p) : R n_p := mul (pow_1576 x) x
def pow_3154 {n_p} (x : R n_p) : R n_p := mul (pow_1577 x) (pow_1577 x)
def pow_6308 {n_p} (x : R n_p) : R n_p := mul (pow_3154 x) (pow_3154 x)
def pow_12616 {n_p} (x : R n_p) : R n_p := mul (pow_6308 x) (pow_6308 x)
def pow_12617 {n_p} (x : R n_p) : R n_p := mul (pow_12616 x) x
def pow_25234 {n_p} (x : R n_p) : R n_p := mul (pow_12617 x) (pow_12617 x)
def pow_25235 {n_p} (x : R n_p) : R n_p := mul (pow_25234 x) x
def pow_50470 {n_p} (x : R n_p) : R n_p := mul (pow_25235 x) (pow_25235 x)
def pow_50471 {n_p} (x : R n_p) : R n_p := mul (pow_50470 x) x
def pow_100942 {n_p} (x : R n_p) : R n_p := mul (pow_50471 x) (pow_50471 x)
def pow_100943 {n_p} (x : R n_p) : R n_p := mul (pow_100942 x) x
theorem pow_2_eq {n_p} (x : R n_p) : pow_2 x = pow x 2 := by
  dsimp [pow_2]
  rw [pow_1_eq, ←pow_add]
theorem pow_3_eq {n_p} (x : R n_p) : pow_3 x = pow x 3 := by
  dsimp [pow_3]
  rw [pow_2_eq]
  rfl
theorem pow_6_eq {n_p} (x : R n_p) : pow_6 x = pow x 6 := by
  dsimp [pow_6]
  rw [pow_3_eq, ←pow_add]
theorem pow_12_eq {n_p} (x : R n_p) : pow_12 x = pow x 12 := by
  dsimp [pow_12]
  rw [pow_6_eq, ←pow_add]
theorem pow_24_eq {n_p} (x : R n_p) : pow_24 x = pow x 24 := by
  dsimp [pow_24]
  rw [pow_12_eq, ←pow_add]
theorem pow_48_eq {n_p} (x : R n_p) : pow_48 x = pow x 48 := by
  dsimp [pow_48]
  rw [pow_24_eq, ←pow_add]
theorem pow_49_eq {n_p} (x : R n_p) : pow_49 x = pow x 49 := by
  dsimp [pow_49]
  rw [pow_48_eq]
  rfl
theorem pow_98_eq {n_p} (x : R n_p) : pow_98 x = pow x 98 := by
  dsimp [pow_98]
  rw [pow_49_eq, ←pow_add]
theorem pow_196_eq {n_p} (x : R n_p) : pow_196 x = pow x 196 := by
  dsimp [pow_196]
  rw [pow_98_eq, ←pow_add]
theorem pow_197_eq {n_p} (x : R n_p) : pow_197 x = pow x 197 := by
  dsimp [pow_197]
  rw [pow_196_eq]
  rfl
theorem pow_394_eq {n_p} (x : R n_p) : pow_394 x = pow x 394 := by
  dsimp [pow_394]
  rw [pow_197_eq, ←pow_add]
theorem pow_788_eq {n_p} (x : R n_p) : pow_788 x = pow x 788 := by
  dsimp [pow_788]
  rw [pow_394_eq, ←pow_add]
theorem pow_1576_eq {n_p} (x : R n_p) : pow_1576 x = pow x 1576 := by
  dsimp [pow_1576]
  rw [pow_788_eq, ←pow_add]
theorem pow_1577_eq {n_p} (x : R n_p) : pow_1577 x = pow x 1577 := by
  dsimp [pow_1577]
  rw [pow_1576_eq]
  rfl
theorem pow_3154_eq {n_p} (x : R n_p) : pow_3154 x = pow x 3154 := by
  dsimp [pow_3154]
  rw [pow_1577_eq, ←pow_add]
theorem pow_6308_eq {n_p} (x : R n_p) : pow_6308 x = pow x 6308 := by
  dsimp [pow_6308]
  rw [pow_3154_eq, ←pow_add]
theorem pow_12616_eq {n_p} (x : R n_p) : pow_12616 x = pow x 12616 := by
  dsimp [pow_12616]
  rw [pow_6308_eq, ←pow_add]
theorem pow_12617_eq {n_p} (x : R n_p) : pow_12617 x = pow x 12617 := by
  dsimp [pow_12617]
  rw [pow_12616_eq]
  rfl
theorem pow_25234_eq {n_p} (x : R n_p) : pow_25234 x = pow x 25234 := by
  dsimp [pow_25234]
  rw [pow_12617_eq, ←pow_add]
theorem pow_25235_eq {n_p} (x : R n_p) : pow_25235 x = pow x 25235 := by
  dsimp [pow_25235]
  rw [pow_25234_eq]
  rfl
theorem pow_50470_eq {n_p} (x : R n_p) : pow_50470 x = pow x 50470 := by
  dsimp [pow_50470]
  rw [pow_25235_eq, ←pow_add]
theorem pow_50471_eq {n_p} (x : R n_p) : pow_50471 x = pow x 50471 := by
  dsimp [pow_50471]
  rw [pow_50470_eq]
  rfl
theorem pow_100942_eq {n_p} (x : R n_p) : pow_100942 x = pow x 100942 := by
  dsimp [pow_100942]
  rw [pow_50471_eq, ←pow_add]
theorem pow_100943_eq {n_p} (x : R n_p) : pow_100943 x = pow x 100943 := by
  dsimp [pow_100943]
  rw [pow_100942_eq]
  rfl
end R
