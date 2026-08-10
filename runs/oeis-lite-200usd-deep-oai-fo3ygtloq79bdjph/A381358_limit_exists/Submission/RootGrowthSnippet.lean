import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open Filter Real
open scoped Topology

example {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    Tendsto (fun n : ℕ => (C * r ^ n) ^ (1 / (n : ℝ))) atTop (𝓝 r) := by
  have hlog : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (C * r ^ n)) atTop (𝓝 (Real.log r)) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log C) atTop (𝓝 0) := by
      simpa [mul_comm, zero_mul] using
        ((tendsto_const_nhds (x := Real.log C)).mul tendsto_one_div_atTop_nhds_zero_nat)
    have h2 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ((n : ℝ) * Real.log r)) atTop (𝓝 (Real.log r)) := by
      have heq : (fun n : ℕ => (1 / (n : ℝ)) * ((n : ℝ) * Real.log r)) =ᶠ[atTop]
          fun _ : ℕ => Real.log r := by
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        field_simp [hn0]
      exact tendsto_const_nhds.congr' heq.symm
    have hsum := h1.add h2
    refine Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hpowpos : 0 < r ^ n := pow_pos hr n
    rw [Real.log_mul hC.ne' hpowpos.ne', Real.log_pow]
    ring
  have hexp := Real.continuous_exp.tendsto (Real.log r)
  refine Tendsto.congr' ?_ (by simpa [Real.exp_log hr] using hexp.comp hlog)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hpos : 0 < C * r ^ n := mul_pos hC (pow_pos hr n)
  rw [Real.rpow_def_of_pos hpos]
  simp [one_div, mul_comm]
