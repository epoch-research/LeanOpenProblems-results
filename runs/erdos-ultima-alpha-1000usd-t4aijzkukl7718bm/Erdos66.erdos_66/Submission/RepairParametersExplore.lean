import FormalConjecturesUtil

/-! The finite repair selection criterion eventually holds at every large
scale, uniformly for O(log N) requested pairs and polynomially many tests. -/
namespace Erdos66RepairParameters
open Filter
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def decay (N : ℕ) : ℝ := (Real.log N) ^ 2 / Real.sqrt N

lemma decay_limit : Tendsto decay atTop (𝓝 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < (1 / 2 : ℝ) by norm_num)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, decay] using hh

lemma scaled_terms_bounds (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (N L m : ℕ) (hN : 2 ≤ N) (hL : (N : ℝ) / 24 ≤ L)
    (hm : (m : ℝ) ≤ D * Real.log N) :
    (m : ℝ) ^ 4 / L ≤ 24 * D ^ 4 * decay N ^ 2 ∧
      ((m : ℝ) * (B * Real.sqrt N * Real.log N)) / L ≤ 24 * D * B * decay N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hLp : (0 : ℝ) < L := lt_of_lt_of_le (by positivity : (0 : ℝ) < N / 24) hL
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hdiv : Real.sqrt (N : ℝ) / N = 1 / Real.sqrt N := by
    field_simp
    nlinarith [Real.sq_sqrt hNp.le]
  constructor
  · calc
      _ ≤ (D * Real.log N) ^ 4 / L :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hm 4) hLp.le
      _ ≤ (D * Real.log N) ^ 4 / ((N : ℝ) / 24) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hL
      _ = _ := by
        dsimp [decay]
        rw [div_pow, Real.sq_sqrt hNp.le]
        field_simp
  · calc
      _ ≤ (D * Real.log N) * (B * Real.sqrt N * Real.log N) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) hLp.le
      _ ≤ (D * Real.log N) * (B * Real.sqrt N * Real.log N) / ((N : ℝ) / 24) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hL
      _ = (24 * D * B * (Real.log N) ^ 2) * (Real.sqrt N / N) := by ring
      _ = _ := by rw [hdiv]; dsimp [decay]; ring

lemma polynomial_exp_log_limit (h : ℕ) :
    Tendsto (fun N : ℕ ↦ ((N : ℝ) ^ h + 1) *
      Real.exp (1 - 2 * ((h : ℝ) + 1) * Real.log N)) atTop (𝓝 0) := by
  have hl : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h₁ := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.Tendsto.const_mul_atTop (show 0 < (h : ℝ) + 2 by positivity) hl)
  have h₂ := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.Tendsto.const_mul_atTop (show 0 < 2 * ((h : ℝ) + 1) by positivity) hl)
  have hh := (h₁.add h₂).const_mul (Real.exp 1)
  simp only [add_zero, mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heN : (N : ℝ) ^ h = Real.exp ((h : ℝ) * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hNp]
  dsimp only [Function.comp_def]
  rw [heN]
  conv_lhs => rw [mul_add]
  conv_rhs => rw [add_mul, one_mul]
  have he₁ : Real.exp 1 * Real.exp (-(((h : ℝ) + 2) * Real.log N)) =
      Real.exp ((h : ℝ) * Real.log N) * Real.exp (1 - 2 * ((h : ℝ) + 1) * Real.log N) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he₂ : Real.exp 1 * Real.exp (-(2 * ((h : ℝ) + 1) * Real.log N)) =
      Real.exp (1 - 2 * ((h : ℝ) + 1) * Real.log N) := by
    rw [← Real.exp_add]
    congr 1
  rw [he₁, he₂]

/-- The tilt is a fixed constant depending on the error and test-range
exponent; no unjustified small-tilt Chernoff bound is used. -/
theorem eventually_selection_small (D B ε : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hε : 0 < ε) (h : ℕ) :
    let t : ℝ := 32 * ((h : ℝ) + 1) / ε
    0 < t ∧ ∀ᶠ N : ℕ in atTop, ∀ L m : ℕ,
      (N : ℝ) / 24 ≤ L → (m : ℝ) ≤ D * Real.log N →
      ((m : ℝ) ^ 4 + m * (B * Real.sqrt N * Real.log N)) / L +
        ((N : ℝ) ^ h + 1) * Real.exp ((m : ℝ) * Real.exp t *
          (B * Real.sqrt N * Real.log N) / L - t * (ε * Real.log N / 16)) < 1 := by
  dsimp only
  let t : ℝ := 32 * ((h : ℝ) + 1) / ε
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨ht, ?_⟩
  have hu : Tendsto (fun N : ℕ ↦ 24 * D ^ 4 * decay N ^ 2 + 24 * D * B * decay N) atTop (𝓝 0) := by
    simpa using ((decay_limit.pow 2).const_mul (24 * D ^ 4)).add (decay_limit.const_mul (24 * D * B))
  have hv : Tendsto (fun N : ℕ ↦ Real.exp t * (24 * D * B * decay N)) atTop (𝓝 0) := by
    simpa using (decay_limit.const_mul (24 * D * B)).const_mul (Real.exp t)
  have he := polynomial_exp_log_limit h
  filter_upwards [eventually_ge_atTop 2, hu.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num),
    hv.eventually_le_const (show (0 : ℝ) < 1 by norm_num),
    he.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)] with N hN huN hvN heN
  intro L m hL hm
  obtain ⟨hb₁, hb₂⟩ := scaled_terms_bounds D B hD hB N L m hN hL hm
  have hbad : ((m : ℝ) ^ 4 + m * (B * Real.sqrt N * Real.log N)) / L < 1 / 2 := by
    rw [add_div]
    linarith
  have hmean : (m : ℝ) * Real.exp t * (B * Real.sqrt N * Real.log N) / L ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hb₂ (Real.exp_pos t).le
    have heq : Real.exp t * ((m : ℝ) * (B * Real.sqrt N * Real.log N) / L) =
        (m : ℝ) * Real.exp t * (B * Real.sqrt N * Real.log N) / L := by ring
    rw [heq] at hh
    exact hh.trans hvN
  have htilt : t * (ε * Real.log N / 16) = 2 * ((h : ℝ) + 1) * Real.log N := by
    dsimp [t]
    field_simp
    ring
  have hexp : Real.exp ((m : ℝ) * Real.exp t * (B * Real.sqrt N * Real.log N) / L -
      t * (ε * Real.log N / 16)) ≤ Real.exp (1 - 2 * ((h : ℝ) + 1) * Real.log N) := by
    apply Real.exp_le_exp.mpr
    rw [htilt]
    linarith
  have hh := mul_le_mul_of_nonneg_left hexp (show 0 ≤ (N : ℝ) ^ h + 1 by positivity)
  change _ + ((N : ℝ) ^ h + 1) * Real.exp ((m : ℝ) * Real.exp t *
    (B * Real.sqrt N * Real.log N) / L - t * (ε * Real.log N / 16)) < 1
  linarith

end Erdos66RepairParameters
