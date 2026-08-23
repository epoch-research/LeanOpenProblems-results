import FormalConjectures.Util.ProblemImports

open Complex Filter Topology Set

private lemma LSeries_real_of_real_coeff (f : ℕ → ℂ)
    (hf : ∀ n, starRingEnd ℂ (f n) = f n) (x : ℝ) :
    starRingEnd ℂ (LSeries f x) = LSeries f x := by
  rw [LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [LSeries.term_def]
  split_ifs with hn0
  · simp
  rw [map_div₀ (starRingEnd ℂ), hf]
  congr 1
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hc : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have harg : ((n : ℂ).arg) ≠ Real.pi := by
    rw [hc, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  simpa using (Complex.conj_cpow (n : ℂ) (x : ℂ) harg).symm

#check LSeries.abscissaOfAbsConv_le_one_of_isBigO_one

private lemma LFunction_real_one_of_real_coeff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hreal : ∀ n : ℕ, starRingEnd ℂ (χ n) = χ n) :
    (χ.LFunction 1).im = 0 := by
  let u : ℕ → ℝ := fun n ↦ 1 + 1 / (n + 1)
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [u] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hcont : ContinuousAt χ.LFunction 1 :=
    (DirichletCharacter.differentiable_LFunction hχ 1).continuousAt
  have hlim : Tendsto (fun n ↦ χ.LFunction (u n)) atTop (𝓝 (χ.LFunction 1)) :=
    hcont.tendsto.comp (Complex.continuous_ofReal.tendsto 1 |>.comp hu)
  have hz : ∀ n, (χ.LFunction (u n)).im = 0 := by
    intro n
    have hu1 : 1 < u n := by simp [u]; positivity
    rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hu1)]
    have hi := Complex.ext_iff.mp
      (LSeries_real_of_real_coeff (fun k ↦ χ k) hreal (u n)) |>.2
    rw [Complex.conj_im] at hi
    linarith
  have hclosed : IsClosed {z : ℂ | z.im = 0} :=
    isClosed_eq continuous_im continuous_const
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hz)

private lemma LFunction_one_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hreal : ∀ n : ℕ, starRingEnd ℂ (χ n) = χ n)
    (hbound : ∀ n : ℕ, ‖χ n‖ ≤ 1) :
    0 < (χ.LFunction 1).re := by
  let f : ℕ → ℂ := fun n ↦ χ n
  have hO : f =O[atTop] (fun _ ↦ (1 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Eventually.of_forall fun n ↦ ?_⟩
    simpa [f] using hbound n
  have hab : LSeries.abscissaOfAbsConv f < ⊤ :=
    (LSeries.abscissaOfAbsConv_le_one_of_isBigO_one hO).trans_lt (EReal.coe_lt_top 1)
  have hlimLS : Tendsto (fun x : ℝ ↦ LSeries f x) atTop (𝓝 1) := by
    simpa [f] using LSeries.tendsto_atTop hab
  have hlim : Tendsto (fun x : ℝ ↦ χ.LFunction x) atTop (𝓝 1) := by
    apply hlimLS.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hx)).symm
  have hlimre : Tendsto (fun x : ℝ ↦ (χ.LFunction x).re) atTop (𝓝 1) :=
    Complex.continuous_re.tendsto 1 |>.comp hlim
  have hevpos : ∀ᶠ x : ℝ in atTop, 0 < (χ.LFunction x).re :=
    hlimre.eventually (Ioi_mem_nhds zero_lt_one)
  obtain ⟨X, hXpos, hX1⟩ :=
    (hevpos.and (eventually_ge_atTop (1 : ℝ))).exists
  have him (x : ℝ) (hx : 1 ≤ x) : (χ.LFunction x).im = 0 := by
    rcases hx.eq_or_lt with rfl | hx
    · exact LFunction_real_one_of_real_coeff χ hχ hreal
    · rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hx)]
      have hi := Complex.ext_iff.mp
        (LSeries_real_of_real_coeff (fun k ↦ χ k) hreal x) |>.2
      rw [Complex.conj_im] at hi
      linarith
  have hne (x : ℝ) (hx : 1 ≤ x) : χ.LFunction x ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using hx)
  by_contra hnpos
  have hone_neg : (χ.LFunction 1).re < 0 := by
    have hne1 := hne 1 le_rfl
    have him1 := him 1 le_rfl
    have : (χ.LFunction 1).re ≠ 0 := by
      intro hre
      apply hne1
      apply Complex.ext <;> simp_all
    exact lt_of_le_of_ne (not_lt.mp hnpos) this
  let g : ℝ → ℝ := fun x ↦ (χ.LFunction x).re
  have hgcont : ContinuousOn g (Icc 1 X) := by
    exact (Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal)).continuousOn
  have hzero_mem : (0 : ℝ) ∈ Icc (g 1) (g X) := ⟨hone_neg.le, hXpos.le⟩
  obtain ⟨y, hy, hy0⟩ := (intermediate_value_Icc hX1 hgcont hzero_mem)
  apply hne y hy.1
  apply Complex.ext
  · simpa [g] using hy0
  · simp [him y hy.1]


private lemma quadratic_LFunction_one_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsQuadratic) (hχne : χ ≠ 1) :
    0 < (χ.LFunction 1).re := by
  apply LFunction_one_re_pos χ hχne
  · intro n
    rcases hχ n with h | h | h <;> simp [h]
  · intro n
    rcases hχ n with h | h | h <;> simp [h]

private lemma quadratic_odd_LFunction_zero_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsQuadratic)
    (hodd : χ.Odd) (hprim : χ.IsPrimitive) (hroot : χ.rootNumber = 1) :
    0 < (χ.LFunction 0).re := by
  have hχne : χ ≠ 1 := by
    intro he
    subst χ
    apply (DirichletCharacter.Odd.not_even (1 : DirichletCharacter ℂ N) hodd)
    exact MulChar.one_apply (isUnit_one.neg)
  have hN : N ≠ 1 := hχne ∘ DirichletCharacter.level_one' χ
  have hL1 : 0 < (χ.LFunction 1).re := quadratic_LFunction_one_re_pos χ hχ hχne
  have hinv : χ⁻¹ = χ := hχ.inv
  have hfe := hprim.completedLFunction_one_sub (1 : ℂ)
  rw [sub_self, hroot, hinv, mul_one] at hfe
  have hgam0 : χ.gammaFactor 0 = 1 := by
    rw [hodd.gammaFactor_def]
    norm_num [Complex.Gammaℝ_one]
  have hgam1 : χ.gammaFactor 1 = (Real.pi : ℂ)⁻¹ := by
    rw [hodd.gammaFactor_def, Complex.Gammaℝ_def]
    norm_num [Complex.Gamma_one, Complex.cpow_neg_one]
  have hcomp0 : χ.completedLFunction 0 = χ.LFunction 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (.inr hN)
    rw [hgam0, div_one] at h
    exact h.symm
  have hcomp1 : χ.completedLFunction 1 = χ.LFunction 1 * (Real.pi : ℂ)⁻¹ := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 1 (.inr hN)
    rw [hgam1, div_inv_eq_mul] at h
    apply (eq_div_iff (by exact_mod_cast Real.pi_ne_zero)).2
    simpa [div_eq_mul_inv] using h.symm
  rw [hcomp0, hcomp1] at hfe
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hpowe : (N : ℂ) ^ ((1 : ℂ) - 1 / 2) =
      (((N : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - 1 / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_cpow hNpos.le (1 / 2 : ℝ)).symm
  rw [hfe, hpowe]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, inv_re, inv_im]
  have hpipos : 0 < Real.pi := Real.pi_pos
  simp only [neg_zero, zero_div, mul_zero, sub_zero]
  rw [Complex.normSq_ofReal]
  have hrpow : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
  positivity


