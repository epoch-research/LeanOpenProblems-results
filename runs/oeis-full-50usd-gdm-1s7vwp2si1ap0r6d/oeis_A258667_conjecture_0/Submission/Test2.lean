import FormalConjectures.Util.ProblemImports

open Asymptotics Filter Topology

theorem simple_eq : (fun n : ℕ ↦ (n : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) + 1) := by
  apply isEquivalent_of_tendsto_one
  · filter_upwards [eventually_ge_atTop 1] with x hx
    intro h
    have : (x : ℝ) + 1 > 0 := by linarith [show (x : ℝ) ≥ 1 by exact_mod_cast hx]
    linarith
  · have h_eq : ((fun x : ℕ ↦ (x : ℝ)) / (fun (x : ℕ) ↦ (x : ℝ) + 1)) =ᶠ[atTop] (fun x ↦ 1 - 1 / ((x : ℝ) + 1)) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      have : (x : ℝ) + 1 ≠ 0 := by linarith [show (x : ℝ) ≥ 1 by exact_mod_cast hx]
      change (x : ℝ) / ((x : ℝ) + 1) = 1 - 1 / ((x : ℝ) + 1)
      field_simp
      ring
    rw [tendsto_congr' h_eq]
    have h_sub : Tendsto (fun (x : ℕ) ↦ 1 - 1 / ((x : ℝ) + 1)) atTop (nhds 1) := by
      have : (1 : ℝ) = 1 - 0 := by ring
      conv_rhs => rw [this]
      refine Tendsto.sub (b := (0 : ℝ)) ?_ ?_
      · exact (tendsto_const_nhds : Tendsto (fun (_ : ℕ) ↦ (1 : ℝ)) atTop (nhds 1))
      · -- Prove Tendsto (fun x ↦ 1 / ((x : ℝ) + 1)) atTop (nhds 0)
        have h_bound : ∀ x ≥ 1, 0 ≤ 1 / ((x : ℝ) + 1) ∧ 1 / ((x : ℝ) + 1) ≤ 1 / (x : ℝ) := by
          intro x hx
          have h_cast : (x : ℝ) ≥ 1 := by exact_mod_cast hx
          have h1 : (x : ℝ) > 0 := by linarith
          have h2 : (x : ℝ) + 1 > 0 := by linarith
          constructor
          · positivity
          · rw [one_div_le_one_div h2 h1]
            linarith
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun (x : ℕ) ↦ 1 / ((x : ℝ) + 1)) (g := fun (_ : ℕ) ↦ (0 : ℝ)) (h := fun (x : ℕ) ↦ 1 / (x : ℝ)) ?_ ?_ ?_ ?_
        · exact (tendsto_const_nhds : Tendsto (fun (_ : ℕ) ↦ (0 : ℝ)) atTop (nhds 0))
        · exact tendsto_one_div_atTop_nhds_zero_nat
        · filter_upwards [eventually_ge_atTop 1] with x hx
          have h_cast : (x : ℝ) ≥ 1 := by exact_mod_cast hx
          exact (h_bound (x : ℝ) h_cast).1
        · filter_upwards [eventually_ge_atTop 1] with x hx
          have h_cast : (x : ℝ) ≥ 1 := by exact_mod_cast hx
          exact (h_bound (x : ℝ) h_cast).2
    exact h_sub
















