import Mathlib
open Nat Filter Topology

lemma tendsto_log_div_n : Tendsto (fun (n : ℕ) => Real.log n / n) atTop (𝓝 0) := by
  have : Tendsto (fun (x : ℝ) => Real.log x / x) atTop (𝓝 0) := Real.tendsto_log_div_x_atTop
  exact this.comp tendsto_natCast_atTop_atTop
