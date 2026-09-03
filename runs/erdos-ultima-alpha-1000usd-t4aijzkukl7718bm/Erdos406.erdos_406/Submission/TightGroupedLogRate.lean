import FormalConjecturesUtil

namespace Erdos406TightGroupedLogRate
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- A numerical threshold only; no construction certificate is asserted. -/
lemma strict_rate : Real.log 2 < (31867/50508 : ℝ) * Real.log 3 := by
  have hn : (2 : ℕ)^50508 < 3^31867 := by decide +kernel
  have hh : (2 : ℝ)^50508 < (3 : ℝ)^31867 := by exact_mod_cast hn
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2^50508) hh
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end Erdos406TightGroupedLogRate
#print axioms Erdos406TightGroupedLogRate.strict_rate
