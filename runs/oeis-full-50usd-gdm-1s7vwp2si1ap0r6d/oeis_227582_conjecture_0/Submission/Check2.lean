import FormalConjectures.Util.ProblemImports

open BigOperators Real Filter Topology

lemma index_le_index (n : ℕ) : n ≤ n * n + n - 1 := by
  rcases n with _ | n
  · simp
  · have h_eq : (n + 1) * (n + 1) + (n + 1) - 1 = (n + 1) * (n + 1) + n := rfl
    rw [h_eq]
    have h1 : n + 1 ≤ (n + 1) * (n + 1) := (n + 1).le_mul_self
    omega

lemma tendsto_index_atTop : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := by
  exact tendsto_atTop_mono index_le_index tendsto_id

lemma tendsto_harmonic_sub_log_comp :
    Tendsto (fun n : ℕ ↦ (harmonic (n * n + n - 1) : ℝ) - log (n * n + n - 1 : ℝ)) atTop (nhds eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) - log n) atTop (nhds eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ ↦ n * n + n - 1) atTop atTop := tendsto_index_atTop
  have h_comp : Tendsto (fun n ↦ (harmonic (n * n + n - 1) : ℝ) - log ↑(n * n + n - 1)) atTop (nhds eulerMascheroniConstant) := h1.comp h2
  have h_eq : (fun n ↦ (harmonic (n * n + n - 1) : ℝ) - log ↑(n * n + n - 1)) =ᶠ[atTop]
              (fun n ↦ (harmonic (n * n + n - 1) : ℝ) - log (n * n + n - 1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    congr 2
    rcases n with _ | n
    · contradiction
    · have h_idx_eq : (n + 1) * (n + 1) + (n + 1) - 1 = (n + 1) * (n + 1) + n := rfl
      rw [h_idx_eq]
      push_cast
      ring
  exact h_comp.congr' h_eq
