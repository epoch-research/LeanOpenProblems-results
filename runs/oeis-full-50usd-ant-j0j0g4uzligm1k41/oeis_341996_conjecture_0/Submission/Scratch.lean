import FormalConjectures.Util.ProblemImports

open Filter Topology Finset

/-- Kronecker's lemma (complex version): if the partial sums `∑_{k<n} b k` converge,
then `(1/N) ∑_{k<N} k • b k → 0`. -/
theorem kronecker_lemma (b : ℕ → ℂ) (L : ℂ)
    (hb : Tendsto (fun n => ∑ k ∈ range n, b k) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ range N, (k : ℂ) * b k) atTop (𝓝 0) := by
  set a : ℕ → ℂ := fun n => ∑ k ∈ range n, b k with ha
  -- Abel summation: ∑_{k<N} k b k = N a_N - ∑_{k<N} a (k+1)  (using a_{k+1}-a_k = b_k)
  have key : ∀ N : ℕ, ∑ k ∈ range N, (k : ℂ) * b k
      = (N : ℂ) * a N - ∑ k ∈ range N, a (k + 1) := by
    intro N
    induction N with
    | zero => simp [ha]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hb' : b n = a (n+1) - a n := by
        simp only [ha, Finset.sum_range_succ]; ring
      rw [hb']
      push_cast
      ring
  -- Cesàro average of the shifted sequence `a (·+1)` tends to `L`.
  have hshift : Tendsto (fun n => a (n + 1)) atTop (𝓝 L) := hb.comp (tendsto_add_atTop_nat 1)
  have hcesaro : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * ∑ k ∈ range n, a (k + 1)) atTop (𝓝 L) := by
    have := hshift.cesaro_smul
    refine this.congr (fun n => ?_)
    rw [Complex.real_smul]
    push_cast
    ring
  -- The main function equals `a N - Cesàro`, eventually.
  have heq : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ range N, (k : ℂ) * b k)
      =ᶠ[atTop] (fun N : ℕ => a N - (N : ℂ)⁻¹ * ∑ k ∈ range N, a (k + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [key N, mul_sub, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_mul]
  rw [tendsto_congr' heq]
  have : L - L = 0 := by ring
  rw [← this]
  exact hb.sub hcesaro
