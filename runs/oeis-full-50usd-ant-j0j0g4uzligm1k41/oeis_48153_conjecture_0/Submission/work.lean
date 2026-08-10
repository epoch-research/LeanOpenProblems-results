import FormalConjectures.Util.ProblemImports

open Complex ArithmeticFunction Filter Topology
open scoped ComplexOrder LSeries.notation ArithmeticFunction.zeta

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- For real `x > 1`, the L-series of the arithmetic function `zetaMul χ` is `> 0`. -/
lemma LSeries_zetaMul_pos (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) {x : ℝ} (hx : 1 < x) :
    0 < LSeries (↗(zetaMul χ)) (x : ℂ) := by
  apply LSeries.positive
  · intro n
    exact zetaMul_nonneg hχ n
  · show 0 < zetaMul χ 1
    rw [(isMultiplicative_zetaMul χ).map_one]
    norm_num
  · -- abscissa ≤ 1 < x
    have hs : (1 : ℝ) < ((( (1+x)/2 : ℝ)) : ℂ).re := by
      simp only [Complex.ofReal_re]; linarith
    have := (LSeriesSummable_zetaMul χ hs).abscissaOfAbsConv_le
    simp only [Complex.ofReal_re] at this
    calc LSeries.abscissaOfAbsConv (↗(zetaMul χ)) ≤ ((1+x)/2 : ℝ) := this
      _ < (x : ℝ) := by exact_mod_cast (by linarith : ((1+x)/2 : ℝ) < x)

/-- `0 < riemannZeta x` for real `x > 1`. -/
lemma riemannZeta_pos {x : ℝ} (hx : 1 < x) : 0 < riemannZeta (x : ℂ) := by
  have hs : (1 : ℝ) < ((x : ℝ) : ℂ).re := by simpa using hx
  rw [← LSeries_zeta_eq_riemannZeta hs]
  apply LSeries.positive
  · intro n
    show (0:ℂ) ≤ ((ζ n : ℕ) : ℂ)
    exact_mod_cast Nat.cast_nonneg (ζ n)
  · show (0:ℂ) < ((ζ 1 : ℕ) : ℂ)
    norm_num
  · have hs2 : (1 : ℝ) < ((( (1+x)/2 : ℝ)) : ℂ).re := by
      simp only [Complex.ofReal_re]; linarith
    have := (LSeriesSummable_zeta_iff.mpr hs2).abscissaOfAbsConv_le
    simp only [Complex.ofReal_re] at this
    calc LSeries.abscissaOfAbsConv (↗ζ) ≤ ((1+x)/2 : ℝ) := this
      _ < (x : ℝ) := by exact_mod_cast (by linarith : ((1+x)/2 : ℝ) < x)

/-- `↗(toArithmeticFunction (χ ·))` agrees with `↗χ` on `n ≠ 0`. -/
lemma coe_toArith_congr (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n ≠ 0) :
    (↗(toArithmeticFunction (χ ·)) : ℕ → ℂ) n = (↗χ) n := by
  show ((toArithmeticFunction (χ ·) n : ℂ)) = (χ n : ℂ)
  rw [← apply_eq_toArithmeticFunction_apply χ hn]

set_option maxHeartbeats 1000000 in
lemma LFunction_pos (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) {x : ℝ} (hx : 1 < x) :
    0 < LFunction χ (x : ℂ) := by
  have hs : (1 : ℝ) < ((x : ℝ) : ℂ).re := by simpa using hx
  have hzsum : LSeriesSummable ↗ζ (x : ℂ) := LSeriesSummable_zeta_iff.mpr hs
  have hχsum : LSeriesSummable (↗(toArithmeticFunction (χ ·))) (x : ℂ) :=
    (LSeriesSummable_congr (x : ℂ) (coe_toArith_congr χ)).mpr
      (LSeriesSummable_of_one_lt_re χ hs)
  have hprod : LSeries (↗(ArithmeticFunction.zeta * toArithmeticFunction (χ ·))) (x : ℂ)
      = LSeries ↗ζ (x : ℂ) * LSeries (↗(toArithmeticFunction (χ ·))) (x : ℂ) :=
    LSeries_mul' hzsum hχsum
  rw [LSeries_congr (coe_toArith_congr χ) (x : ℂ),
      LSeries_zeta_eq_riemannZeta hs, ← LFunction_eq_LSeries χ hs] at hprod
  have hpos := LSeries_zetaMul_pos χ hχ hx
  rw [show zetaMul χ = ArithmeticFunction.zeta * toArithmeticFunction (χ ·) from rfl,
      hprod] at hpos
  exact (mul_pos_iff_of_pos_left (riemannZeta_pos hx)).mp hpos

/-- **`L(1,χ) > 0` for a nontrivial quadratic Dirichlet character.** -/
theorem LFunction_one_pos (χ : DirichletCharacter ℂ N) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    0 < LFunction χ 1 := by
  have hcont : ContinuousAt (LFunction χ) 1 := (differentiable_LFunction hχ1 1).continuousAt
  have h1 : Tendsto (fun x : ℝ => ((x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have htends : Tendsto (fun x : ℝ => LFunction χ (x : ℂ)) (𝓝[>] 1) (𝓝 (LFunction χ 1)) :=
    hcont.tendsto.comp h1
  -- real part limit is ≥ 0
  have hre : (0 : ℝ) ≤ (LFunction χ 1).re := by
    refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp htends) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Complex.pos_iff.mp (LFunction_pos χ hχ2 hx)).1.le
  -- imaginary part limit is 0
  have him : (LFunction χ 1).im = 0 := by
    have htim : Tendsto (fun x : ℝ => (LFunction χ (x : ℂ)).im) (𝓝[>] 1)
        (𝓝 (LFunction χ 1).im) := (Complex.continuous_im.tendsto _).comp htends
    have htim0 : Tendsto (fun x : ℝ => (LFunction χ (x : ℂ)).im) (𝓝[>] 1) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact ((Complex.pos_iff.mp (LFunction_pos χ hχ2 hx)).2)
    exact tendsto_nhds_unique htim htim0
  -- combine with nonvanishing
  rw [Complex.pos_iff]
  refine ⟨?_, him.symm⟩
  rcases lt_or_eq_of_le hre with h | h
  · exact h
  · exfalso
    have hz : LFunction χ 1 = 0 := by
      apply Complex.ext
      · simpa using h.symm
      · simpa using him
    exact LFunction_apply_one_ne_zero hχ1 hz

