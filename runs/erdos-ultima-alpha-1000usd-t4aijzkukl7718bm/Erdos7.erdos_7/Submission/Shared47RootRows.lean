import Submission.Shared47Data

namespace Erdos7Shared47Rows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def geoRoot : ℚ := (2/5)*mixture 5 1 (1/5) stage7.F 1 +
  (2/5)*mixture 5 1 (1/5) stage7.F 2 + (1/5)*mixture 5 1 (1/5) stage7.F 3

def shortRoot : ℚ := 2/5 + (7/100)*evaluate stage7.F 1 +
  (22/100)*evaluate stage7.F 2 + (11/100)*evaluate stage7.F 3 + geoRoot

def longRoot : ℚ := 9/20 + (13/100)*evaluate stage7.F 1 +
  (15/100)*evaluate stage7.F 2 + (7/100)*evaluate stage7.F 3 + geoRoot

def flatRoot : ℚ := 1/4 + (11/50)*evaluate stage7.F 1 +
  (11/50)*evaluate stage7.F 2 + (11/100)*evaluate stage7.F 3 + geoRoot

theorem shortRoot_exact : shortRoot = (23776688561519854305619981/23841857910156250000000000 : ℚ) := by decide +kernel
theorem shortRoot_lt_one : shortRoot < 1 := by rw [shortRoot_exact]; norm_num
theorem longRoot_exact : longRoot = (23800929203113787411088731/23841857910156250000000000 : ℚ) := by decide +kernel
theorem longRoot_lt_one : longRoot < 1 := by rw [longRoot_exact]; norm_num
theorem flatRoot_exact : flatRoot = (11441313504020806669411553/11920928955078125000000000 : ℚ) := by decide +kernel
theorem flatRoot_lt_one : flatRoot < 1 := by rw [flatRoot_exact]; norm_num
end Erdos7Shared47Rows
