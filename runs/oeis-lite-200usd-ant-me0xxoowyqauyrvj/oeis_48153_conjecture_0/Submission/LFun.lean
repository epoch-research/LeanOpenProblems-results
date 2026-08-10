import FormalConjectures.Util.ProblemImports

open Complex Filter Topology ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.zeta

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- For `1 < s.re`, `LSeries (zetaMul χ) s = riemannZeta s * L(χ, s)`. -/
theorem LSeries_zetaMul_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(zetaMul χ) s = riemannZeta s * χ.LFunction s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · rw [χ.LFunction_eq_LSeries hs]
      exact LSeries_congr (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm) s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

open scoped ComplexOrder

/-- `riemannZeta x > 0` for real `x > 1`. -/
theorem riemannZeta_pos_of_one_lt {x : ℝ} (hx : 1 < x) : (0 : ℂ) < riemannZeta x := by
  rw [← LSeries_zeta_eq_riemannZeta (by simpa using hx)]
  refine LSeries.positive (a := ↗ζ) (fun n => ?_) ?_ ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [zeta_apply_ne hn, Nat.cast_one]; exact zero_le_one
  · simp only [zeta_apply_ne one_ne_zero, Nat.cast_one]; exact zero_lt_one
  · rw [abscissaOfAbsConv_zeta]; exact_mod_cast hx

/-- For real `x > 1` and quadratic `χ`, `L(χ, x)` is a positive real. -/
theorem LFunction_pos_of_quadratic {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) {x : ℝ} (hx : 1 < x) :
    (0 : ℂ) < χ.LFunction x := by
  have hz : (0 : ℂ) < riemannZeta x := riemannZeta_pos_of_one_lt hx
  have hzm : (0 : ℂ) < LSeries ↗(zetaMul χ) x := by
    refine LSeries.positive (fun n => zetaMul_nonneg hχ n) ?_ ?_
    · exact χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one
    · refine lt_of_le_of_lt ?_ (by exact_mod_cast hx : (1 : EReal) < (x : ℝ))
      exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        fun _ a => χ.LSeriesSummable_zetaMul a
  rw [LSeries_zetaMul_eq χ (by simpa using hx)] at hzm
  exact (mul_pos_iff_of_pos_left hz).mp hzm

/-- For a nontrivial quadratic character `χ`, `L(χ, 1) > 0`. -/
theorem LFunction_one_pos {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    (0 : ℂ) < χ.LFunction 1 := by
  -- continuity of `x ↦ L(χ, x)` at `1`
  have hcont : ContinuousAt (fun x : ℝ => χ.LFunction x) 1 := by
    have h1 : ContinuousAt χ.LFunction (((1 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_one]
      exact (χ.differentiableAt_LFunction 1 (Or.inr hχ1)).continuousAt
    exact h1.comp Complex.continuous_ofReal.continuousAt
  have htend : Tendsto (fun x : ℝ => χ.LFunction x) (𝓝[>] 1) (𝓝 (χ.LFunction 1)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- eventually positive on `(1, ∞)`
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 1, (0 : ℂ) < χ.LFunction x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact LFunction_pos_of_quadratic hχ hx
  -- imaginary part is `0` in the limit
  have him : (χ.LFunction 1).im = 0 := by
    have h1 : Tendsto (fun x : ℝ => (χ.LFunction x).im) (𝓝[>] 1) (𝓝 (χ.LFunction 1).im) :=
      (Complex.continuous_im.continuousAt.tendsto).comp htend
    have h2 : (fun x : ℝ => (χ.LFunction x).im) =ᶠ[𝓝[>] 1] (fun _ => 0) := by
      filter_upwards [hev] with x hx
      exact ((Complex.pos_iff).mp hx).2.symm
    exact tendsto_nhds_unique (h1.congr' h2) tendsto_const_nhds
  -- real part is `≥ 0` in the limit
  have hre : 0 ≤ (χ.LFunction 1).re := by
    have h1 : Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 (χ.LFunction 1).re) :=
      (Complex.continuous_re.continuousAt.tendsto).comp htend
    refine ge_of_tendsto h1 ?_
    filter_upwards [hev] with x hx
    exact ((Complex.pos_iff).mp hx).1.le
  -- nonvanishing
  have hne : χ.LFunction 1 ≠ 0 := LFunction_apply_one_ne_zero hχ1
  rw [Complex.pos_iff]
  refine ⟨hre.lt_of_ne ?_, him.symm⟩
  intro h
  exact hne (Complex.ext_iff.mpr ⟨by rw [Complex.zero_re]; exact h.symm,
    by rw [Complex.zero_im]; exact him⟩)

end DirichletCharacter
