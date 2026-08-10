import FormalConjectures.Util.ProblemImports
open List Nat Filter

/-! Abstract analysis: from a positive 3-variable linear system with bounded perturbation,
derive two-sided geometric bounds and the limit of the n-th root. -/

namespace Dev

/-- The eigenvalue: a real root > 1 of x^4 (x-1)^3 = 1. -/
theorem exists_lambda : ∃ l : ℝ, 1 < l ∧ l < 2 ∧ l^4 * (l-1)^3 = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x^4 * (x-1)^3 - 1) (Set.Icc 1 2) := by fun_prop
  have h1 : (fun x : ℝ => x^4 * (x-1)^3 - 1) 1 ≤ 0 := by norm_num
  have h2 : (0:ℝ) ≤ (fun x : ℝ => x^4 * (x-1)^3 - 1) 2 := by norm_num
  obtain ⟨c, hc, hroot⟩ := intermediate_value_Icc (by norm_num) hcont (Set.mem_Icc.2 ⟨h1, h2⟩)
  refine ⟨c, ?_, ?_, by linarith [hroot]⟩
  · rcases hc.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hroot; norm_num at hroot
  · rcases hc.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h] at hroot; norm_num at hroot

section Analysis
variable (lam : ℝ) (ell r q : ℕ → ℝ)

/-- The linear functional (left eigenvector applied to the state). -/
noncomputable def Y (n : ℕ) : ℝ :=
  ell (n+4) + (lam-1)*ell (n+3) + lam*(lam-1)*ell (n+2) + lam^2*(lam-1)*ell (n+1)
    + lam^3*(lam-1)*ell n + (1/(lam-1)) * r (n+4) + lam^4*(lam-1) * q (n+4)

variable {lam ell r q}

/-- Key step: Y satisfies an affine recurrence Y(n+1) = lam * Y n - 1/(lam-1). -/
theorem Y_step (hlam1 : 1 < lam) (key : lam^4*(lam-1)^3 = 1) {N n : ℕ} (hn : N ≤ n)
    (hR1 : ∀ m, N ≤ m → ell (m+1) = ell m + r m)
    (hR2 : ∀ m, N ≤ m → r (m+1) = r m + q m - 1)
    (hR3 : ∀ m, N ≤ m → q (m+5) = q (m+4) + ell m) :
    Y lam ell r q (n+1) = lam * Y lam ell r q n - 1/(lam-1) := by
  have hlne : lam - 1 ≠ 0 := by linarith
  have e1 : ell (n+5) = ell (n+4) + r (n+4) := hR1 (n+4) (by omega)
  have e2 : r (n+5) = r (n+4) + q (n+4) - 1 := hR2 (n+4) (by omega)
  have e3 : q (n+5) = q (n+4) + ell n := hR3 n hn
  show ell (n+5) + (lam-1)*ell (n+4) + lam*(lam-1)*ell (n+3) + lam^2*(lam-1)*ell (n+2)
        + lam^3*(lam-1)*ell (n+1) + (1/(lam-1)) * r (n+5) + lam^4*(lam-1) * q (n+5)
       = lam * (ell (n+4) + (lam-1)*ell (n+3) + lam*(lam-1)*ell (n+2) + lam^2*(lam-1)*ell (n+1)
        + lam^3*(lam-1)*ell n + (1/(lam-1)) * r (n+4) + lam^4*(lam-1) * q (n+4)) - 1/(lam-1)
  rw [e1, e2, e3]
  field_simp
  linear_combination (-(q (n+4))) * key

/-- Closed form: Y(N+k) = lam^k * (Y N - c0) + c0, with c0 = 1/(lam-1)^2. -/
theorem Y_closed (hlam1 : 1 < lam) (key : lam^4*(lam-1)^3 = 1) {N : ℕ}
    (hR1 : ∀ m, N ≤ m → ell (m+1) = ell m + r m)
    (hR2 : ∀ m, N ≤ m → r (m+1) = r m + q m - 1)
    (hR3 : ∀ m, N ≤ m → q (m+5) = q (m+4) + ell m) (k : ℕ) :
    Y lam ell r q (N+k) - 1/(lam-1)^2 = lam^k * (Y lam ell r q N - 1/(lam-1)^2) := by
  have hlne : lam - 1 ≠ 0 := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := Y_step hlam1 key (N := N) (n := N+k) (by omega) hR1 hR2 hR3
    have hY : Y lam ell r q (N+(k+1)) = lam * Y lam ell r q (N+k) - 1/(lam-1) := by
      rw [show N+(k+1) = (N+k)+1 from by ring]; exact hstep
    rw [hY, pow_succ]
    have ihv : Y lam ell r q (N+k) = lam^k * (Y lam ell r q N - 1/(lam-1)^2) + 1/(lam-1)^2 := by
      linarith [ih]
    rw [ihv]
    field_simp
    ring

/-- Monotonicity helper. -/
theorem ell_mono_add {N : ℕ} (hmono : ∀ m, N ≤ m → ell m ≤ ell (m+1))
    (a : ℕ) (ha : N ≤ a) : ∀ d, ell a ≤ ell (a+d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    calc ell a ≤ ell (a+d) := ih
      _ ≤ ell (a+d+1) := hmono (a+d) (by omega)

/-- Main two-sided geometric bound for ell. -/
theorem ell_geom_bounds (hlam1 : 1 < lam) (hlam2 : lam < 2) (key : lam^4*(lam-1)^3 = 1)
    {N : ℕ}
    (hR1 : ∀ m, N ≤ m → ell (m+1) = ell m + r m)
    (hR2 : ∀ m, N ≤ m → r (m+1) = r m + q m - 1)
    (hR3 : ∀ m, N ≤ m → q (m+5) = q (m+4) + ell m)
    (hpos : ∀ m, N ≤ m → 0 ≤ q m ∧ q m ≤ r m ∧ r m ≤ ell m)
    (hmono : ∀ m, N ≤ m → ell m ≤ ell (m+1))
    (hbase : (17:ℝ) ≤ ell (N+4)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m, N+4 ≤ m → c * lam^m ≤ ell m ∧ ell m ≤ C * lam^m := by
  have hlne : (0:ℝ) < lam - 1 := by linarith
  have hl0 : (0:ℝ) < lam := by linarith
  set c0 : ℝ := 1/(lam-1)^2 with hc0def
  -- c0 < 16
  have hsq : (lam-1)^2 = 1/(lam^4*(lam-1)) := by
    have : lam^4 * (lam-1) ≠ 0 := by positivity
    field_simp
    linear_combination key
  have c0pos : 0 < c0 := by rw [hc0def]; positivity
  have hlam2sq : lam^2 < 4 := by nlinarith
  have hlam4 : lam^4 < 16 := by nlinarith [hlam2sq, sq_nonneg lam]
  have hprod : lam^4*(lam-1) < 16 := by nlinarith [hlam4, hlne, (show lam-1<1 by linarith), hl0]
  have hprodpos : (0:ℝ) < lam^4*(lam-1) := by positivity
  have hsqlb : (lam-1)^2 > 1/16 := by
    rw [hsq, gt_iff_lt]; exact one_div_lt_one_div_of_lt hprodpos hprod
  have hc0 : c0 < 16 := by
    rw [hc0def]
    calc 1/(lam-1)^2 < 1/(1/16) := one_div_lt_one_div_of_lt (by norm_num) hsqlb
      _ = 16 := by norm_num
  -- Y N ≥ ell (N+4)
  have hellnn : ∀ m, N ≤ m → 0 ≤ ell m := fun m hm => le_trans (le_trans (hpos m hm).1 (hpos m hm).2.1) (hpos m hm).2.2
  have hYN_ge : ell (N+4) ≤ Y lam ell r q N := by
    simp only [Y]
    have h3 := hellnn (N+3) (by omega)
    have h2 := hellnn (N+2) (by omega)
    have h1 := hellnn (N+1) (by omega)
    have h0 := hellnn N (by omega)
    have hr := (hpos (N+4) (by omega)).2.2
    have hq := (hpos (N+4) (by omega)).1
    have hrnn : 0 ≤ r (N+4) := le_trans hq (hpos (N+4) (by omega)).2.1
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ lam-1) h3,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam*(lam-1)) h2,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^2*(lam-1)) h1,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^3*(lam-1)) h0,
      mul_nonneg (by positivity : (0:ℝ) ≤ 1/(lam-1)) hrnn,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^4*(lam-1)) hq]
  set d : ℝ := Y lam ell r q N - c0 with hddef
  have hd : 0 < d := by rw [hddef]; linarith [hYN_ge, hbase, hc0]
  -- S coefficient sum
  set S : ℝ := 1 + (lam-1) + lam*(lam-1) + lam^2*(lam-1) + lam^3*(lam-1) + 1/(lam-1) + lam^4*(lam-1) with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  refine ⟨d/(S*lam^(N+4)), (d+c0)/lam^(N+4), by positivity, by positivity, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m-4, by omega⟩
  have hnN : N ≤ n := by omega
  -- Y n closed form
  have hclosed : Y lam ell r q n = lam^(n-N) * d + c0 := by
    have := Y_closed hlam1 key hR1 hR2 hR3 (n-N)
    rw [show N + (n-N) = n from by omega] at this
    rw [hddef]; linarith [this]
  have hpow1 : (1:ℝ) ≤ lam^(n-N) := one_le_pow₀ (le_of_lt hlam1)
  have hpowsplit : lam^(n+4) = lam^(N+4) * lam^(n-N) := by
    rw [← pow_add]; congr 1; omega
  have hYpos : 0 < Y lam ell r q n := by rw [hclosed]; positivity
  -- ell (n+4) ≤ Y n
  have hupper1 : ell (n+4) ≤ Y lam ell r q n := by
    simp only [Y]
    have h3 := hellnn (n+3) (by omega)
    have h2 := hellnn (n+2) (by omega)
    have h1 := hellnn (n+1) (by omega)
    have h0 := hellnn n (by omega)
    have hq := (hpos (n+4) (by omega)).1
    have hrnn : 0 ≤ r (n+4) := le_trans hq (hpos (n+4) (by omega)).2.1
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ lam-1) h3,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam*(lam-1)) h2,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^2*(lam-1)) h1,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^3*(lam-1)) h0,
      mul_nonneg (by positivity : (0:ℝ) ≤ 1/(lam-1)) hrnn,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^4*(lam-1)) hq]
  -- Y n ≤ S * ell (n+4)
  have hlower1 : Y lam ell r q n ≤ S * ell (n+4) := by
    have m3 : ell (n+3) ≤ ell (n+4) := by have := ell_mono_add hmono (n+3) (by omega) 1; simpa using this
    have m2 : ell (n+2) ≤ ell (n+4) := by have := ell_mono_add hmono (n+2) (by omega) 2; simpa using this
    have m1 : ell (n+1) ≤ ell (n+4) := by have := ell_mono_add hmono (n+1) (by omega) 3; simpa using this
    have m0 : ell n ≤ ell (n+4) := by have := ell_mono_add hmono n (by omega) 4; simpa using this
    have hrle : r (n+4) ≤ ell (n+4) := (hpos (n+4) (by omega)).2.2
    have hqle : q (n+4) ≤ ell (n+4) := le_trans (hpos (n+4) (by omega)).2.1 hrle
    have expand : S * ell (n+4) = ell (n+4) + (lam-1)*ell (n+4) + lam*(lam-1)*ell (n+4)
        + lam^2*(lam-1)*ell (n+4) + lam^3*(lam-1)*ell (n+4) + (1/(lam-1))*ell (n+4)
        + lam^4*(lam-1)*ell (n+4) := by rw [hSdef]; ring
    rw [expand]
    simp only [Y]
    linarith [mul_le_mul_of_nonneg_left m3 (by positivity : (0:ℝ) ≤ lam-1),
      mul_le_mul_of_nonneg_left m2 (by positivity : (0:ℝ) ≤ lam*(lam-1)),
      mul_le_mul_of_nonneg_left m1 (by positivity : (0:ℝ) ≤ lam^2*(lam-1)),
      mul_le_mul_of_nonneg_left m0 (by positivity : (0:ℝ) ≤ lam^3*(lam-1)),
      mul_le_mul_of_nonneg_left hrle (by positivity : (0:ℝ) ≤ 1/(lam-1)),
      mul_le_mul_of_nonneg_left hqle (by positivity : (0:ℝ) ≤ lam^4*(lam-1))]
  constructor
  · -- lower: d/(S lam^(N+4)) * lam^(n+4) ≤ ell(n+4)
    have hYlb : lam^(n-N) * d ≤ Y lam ell r q n := by rw [hclosed]; linarith [c0pos]
    have : d/(S*lam^(N+4)) * lam^(n+4) ≤ Y lam ell r q n / S := by
      rw [hpowsplit]
      rw [div_mul_eq_mul_div, le_div_iff₀ hS]
      have : d * (lam^(N+4)*lam^(n-N)) / (S*lam^(N+4)) * S = d * lam^(n-N) := by
        field_simp
      rw [this]
      calc d * lam^(n-N) = lam^(n-N)*d := by ring
        _ ≤ Y lam ell r q n := hYlb
    calc d/(S*lam^(N+4)) * lam^(n+4) ≤ Y lam ell r q n / S := this
      _ ≤ ell (n+4) := by rw [div_le_iff₀ hS]; linarith [hlower1]
  · -- upper: ell(n+4) ≤ (d+c0)/lam^(N+4) * lam^(n+4)
    have hYub : Y lam ell r q n ≤ lam^(n-N) * (d+c0) := by
      have hmul : c0 ≤ lam^(n-N) * c0 := le_mul_of_one_le_left c0pos.le hpow1
      have hexp : lam^(n-N) * (d+c0) = lam^(n-N) * d + lam^(n-N) * c0 := by ring
      rw [hclosed, hexp]; linarith [hmul]
    calc ell (n+4) ≤ Y lam ell r q n := hupper1
      _ ≤ lam^(n-N) * (d+c0) := hYub
      _ = (d+c0)/lam^(N+4) * lam^(n+4) := by rw [hpowsplit]; field_simp; try ring

/-- `a^(1/n) → 1` for `a > 0`. -/
theorem tendsto_rpow_inv_one {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => a^((n:ℝ)⁻¹)) atTop (nhds 1) := by
  have h0 : Tendsto (fun n : ℕ => Real.log a * (n:ℝ)⁻¹) atTop (nhds 0) := by
    have hb : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := Real.log a)).mul hb
    simpa using this
  have hcont : Tendsto (fun x : ℝ => Real.exp x) (nhds 0) (nhds 1) := by
    have := Real.continuous_exp.tendsto 0
    simpa using this
  have := hcont.comp h0
  refine this.congr (fun n => ?_)
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos ha]

/-- Geometric two-sided bounds give the limit of the n-th root. -/
theorem tendsto_rpow_of_geom_bounds {lam c C : ℝ} (hlam : 1 < lam) (hc : 0 < c) (hC : 0 < C)
    {M : ℕ} {f : ℕ → ℝ} (hb : ∀ m, M ≤ m → c * lam^m ≤ f m ∧ f m ≤ C * lam^m) :
    Tendsto (fun n : ℕ => (f n)^((n:ℝ)⁻¹)) atTop (nhds lam) := by
  have hl0 : (0:ℝ) ≤ lam := by linarith
  have hlow : Tendsto (fun n : ℕ => c^((n:ℝ)⁻¹) * lam) atTop (nhds lam) := by
    have := (tendsto_rpow_inv_one hc).mul_const lam
    simpa using this
  have hupp : Tendsto (fun n : ℕ => C^((n:ℝ)⁻¹) * lam) atTop (nhds lam) := by
    have := (tendsto_rpow_inv_one hC).mul_const lam
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop (max M 1)] with n hn
    have hnM : M ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hfpos : 0 < f n := lt_of_lt_of_le (by positivity) (hb n hnM).1
    -- c^(1/n) * lam = (c * lam^n)^(1/n) ≤ (f n)^(1/n)
    have hrw : c^((n:ℝ)⁻¹) * lam = (c * lam^n)^((n:ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast lam n, ← Real.rpow_mul hl0]
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))]
      simp
    rw [hrw]
    exact Real.rpow_le_rpow (by positivity) (hb n hnM).1 (by positivity)
  · filter_upwards [eventually_ge_atTop (max M 1)] with n hn
    have hnM : M ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hfpos : 0 ≤ f n := le_trans (by positivity) (hb n hnM).1
    have hrw : C^((n:ℝ)⁻¹) * lam = (C * lam^n)^((n:ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast lam n, ← Real.rpow_mul hl0]
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))]
      simp
    rw [hrw]
    exact Real.rpow_le_rpow hfpos (hb n hnM).2 (by positivity)

end Analysis

end Dev
