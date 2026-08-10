import FormalConjectures.Util.ProblemImports
open Filter Asymptotics
open scoped Topology
example : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have hgf : ∀ᶠ x : ℝ in atTop, id x = 0 → Real.log x = 0 := by
    filter_upwards [eventually_ne_atTop (0:ℝ)] with x hx h0
    exact False.elim (hx h0)
  simpa [id] using ((isLittleO_iff_tendsto' (f := Real.log) (g := id) hgf).mp Real.isLittleO_log_id_atTop)
