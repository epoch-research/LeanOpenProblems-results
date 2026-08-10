import FormalConjectures.Util.ProblemImports
open scoped Interval
open MeasureTheory intervalIntegral Filter


lemma deriv_tpow (r : ℕ) : deriv (fun x : ℝ => (x * (1 - x)) ^ r) =
    fun x => (r : ℝ) * (x * (1 - x)) ^ (r - 1) * (1 - 2 * x) := by
  funext x
  by_cases hr : r = 0
  · subst r
    simp
  · have hder : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
      convert ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))) using 1
      · simp
        ring
    have hp := hder.pow r
    rw [deriv]
    exact hp.deriv

example (r : ℕ) :
    (∫ x in (0:ℝ)..1, Real.exp x * deriv (fun y : ℝ => (y * (1 - y)) ^ r) x)
      = Real.exp 1 * ((1:ℝ) * (1 - 1)) ^ r - Real.exp 0 * ((0:ℝ) * (1 - 0)) ^ r
        - ∫ x in (0:ℝ)..1, Real.exp x * ((x * (1 - x)) ^ r) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp x) (u' := fun x : ℝ => Real.exp x)
    (v := fun x : ℝ => (x * (1 - x)) ^ r)
    (v' := fun x : ℝ => deriv (fun y : ℝ => (y * (1 - y)) ^ r) x)
    (a := (0:ℝ)) (b := (1:ℝ))
    (hu := by intro x hx; exact Real.hasDerivAt_exp x)
    (hv := by intro x hx; exact (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y * (1 - y)) ^ r) x).hasDerivAt)
    (hu' := by exact Continuous.intervalIntegrable (by fun_prop) 0 1)
    (hv' := by
      rw [deriv_tpow]
      exact Continuous.intervalIntegrable (by fun_prop) 0 1)
  simpa using h


lemma integral_exp_deriv2_eq (r : ℕ) (hr : 2 ≤ r) :
    (∫ x in (0:ℝ)..1, Real.exp x * deriv (deriv (fun y : ℝ => (y * (1 - y)) ^ r)) x)
      = ∫ x in (0:ℝ)..1, Real.exp x * ((x * (1 - x)) ^ r) := by
  let φ : ℝ → ℝ := fun y => (y * (1 - y)) ^ r
  have hφ0 : φ 0 = 0 := by
    dsimp [φ]
    have : r ≠ 0 := by omega
    simp [this]
  have hφ1 : φ 1 = 0 := by
    dsimp [φ]
    have : r ≠ 0 := by omega
    simp [this]
  have hdφ0 : deriv φ 0 = 0 := by
    dsimp [φ]
    rw [deriv_tpow]
    have : r - 1 ≠ 0 := by omega
    simp [this]
  have hdφ1 : deriv φ 1 = 0 := by
    dsimp [φ]
    rw [deriv_tpow]
    have : r - 1 ≠ 0 := by omega
    simp [this]
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp x) (u' := fun x : ℝ => Real.exp x)
    (v := φ) (v' := fun x : ℝ => deriv φ x)
    (a := (0:ℝ)) (b := (1:ℝ))
    (hu := by intro x hx; exact Real.hasDerivAt_exp x)
    (hv := by intro x hx; exact (by dsimp [φ]; fun_prop : DifferentiableAt ℝ φ x).hasDerivAt)
    (hu' := by exact Continuous.intervalIntegrable (by fun_prop) 0 1)
    (hv' := by
      dsimp [φ]
      rw [deriv_tpow]
      exact Continuous.intervalIntegrable (by fun_prop) 0 1)
  have ibp1' : (∫ x in (0:ℝ)..1, Real.exp x * deriv φ x) = - ∫ x in (0:ℝ)..1, Real.exp x * φ x := by
    rw [ibp1, hφ0, hφ1]
    simp
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp x) (u' := fun x : ℝ => Real.exp x)
    (v := fun x : ℝ => deriv φ x) (v' := fun x : ℝ => deriv (deriv φ) x)
    (a := (0:ℝ)) (b := (1:ℝ))
    (hu := by intro x hx; exact Real.hasDerivAt_exp x)
    (hv := by
      intro x hx
      dsimp [φ]
      rw [deriv_tpow]
      exact (by fun_prop : DifferentiableAt ℝ (fun x => (r : ℝ) * (x * (1 - x)) ^ (r - 1) * (1 - 2 * x)) x).hasDerivAt)
    (hu' := by exact Continuous.intervalIntegrable (by fun_prop) 0 1)
    (hv' := by
      dsimp [φ]
      rw [deriv_tpow]
      exact Continuous.intervalIntegrable (by fun_prop) 0 1)
  rw [ibp2, hdφ0, hdφ1]
  rw [ibp1']
  simp [φ]

-- copied second derivative lemmas
lemma deriv_second_aux (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1) * (1 - 2 * y)) x =
      (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  have hpow : deriv (fun y : ℝ => (y * (1 - y)) ^ (r - 1)) x =
      ((r - 1 : ℕ) : ℝ) * (x * (1 - x)) ^ ((r - 1) - 1) * (1 - 2 * x) := by
    simpa using congrFun (deriv_tpow (r - 1)) x
  have hconst : deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1)) x =
      (r : ℝ) * deriv (fun y : ℝ => (y * (1 - y)) ^ (r - 1)) x := by
    rw [deriv_const_mul]
    fun_prop
  have hlin : deriv (fun y : ℝ => 1 - 2 * y) x = -2 := by
    have h : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
      convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x)) using 1
      · norm_num
    exact h.deriv
  change deriv (((fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1)) *
      (fun y : ℝ => 1 - 2 * y))) x = _
  rw [deriv_mul (c := fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1))
      (d := fun y : ℝ => 1 - 2 * y)]
  · rw [hconst, hpow, hlin]
    have h1 : r - 1 - 1 = r - 2 := by omega
    have hcast : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [h1, hcast]
    ring
  · fun_prop
  · fun_prop

lemma deriv2_tpow_chain (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  funext x
  rw [deriv_tpow]
  exact deriv_second_aux r hr x

lemma deriv2_tpow_expanded (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2)
        - (2 * (r : ℝ) * (2 * (r : ℝ) - 1)) * (x * (1 - x)) ^ (r - 1) := by
  rw [deriv2_tpow_chain r hr]
  funext x
  have hpow : (x * (1 - x)) ^ (r - 1) = (x * (1 - x)) ^ (r - 2) * (x * (1 - x)) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
  rw [hpow]
  ring

noncomputable def K (r : ℕ) : ℝ := ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ r

lemma K_recurrence (r : ℕ) (hr : 2 ≤ r) :
    K r = (r : ℝ) * (r - 1 : ℝ) * K (r - 2) - (2 * (r : ℝ) * (2 * (r : ℝ) - 1)) * K (r - 1) := by
  have h := (integral_exp_deriv2_eq r hr).symm
  rw [deriv2_tpow_expanded r hr] at h
  dsimp [K]
  rw [h]
  simp only [Pi.sub_apply, mul_sub]
  rw [intervalIntegral.integral_sub]
  · let c : ℝ := (r : ℝ) * (r - 1 : ℝ)
    let d : ℝ := (2 * (r : ℝ) * (2 * (r : ℝ) - 1))
    have hA : (∫ x in (0:ℝ)..1, Real.exp x * (c * (x * (1 - x)) ^ (r - 2))) =
        c * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hB : (∫ x in (0:ℝ)..1, Real.exp x * (d * (x * (1 - x)) ^ (r - 1))) =
        d * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hA' : (∫ x in (0:ℝ)..1, Real.exp x * (((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * (x * 1 - x * x) ^ (r - 2))) =
        ((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 2) := by
      calc
        (∫ x in (0:ℝ)..1, Real.exp x * (((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * (x * 1 - x * x) ^ (r - 2)))
            = ∫ x in (0:ℝ)..1, Real.exp x * (c * (x * (1 - x)) ^ (r - 2)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [c]
              ring
        _ = c * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 2) := hA
        _ = ((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 2) := by
              dsimp [c]
              ring_nf
    have hB' : (∫ x in (0:ℝ)..1, Real.exp x * (((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * (x * 1 - x * x) ^ (r - 1))) =
        ((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 1) := by
      calc
        (∫ x in (0:ℝ)..1, Real.exp x * (((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * (x * 1 - x * x) ^ (r - 1)))
            = ∫ x in (0:ℝ)..1, Real.exp x * (d * (x * (1 - x)) ^ (r - 1)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [d]
              ring
        _ = d * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 1) := hB
        _ = ((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 1) := by
              dsimp [d]
              ring_nf
    rw [hA', hB']
  · exact Continuous.intervalIntegrable (by fun_prop) 0 1
  · exact Continuous.intervalIntegrable (by fun_prop) 0 1


noncomputable def S (m : ℕ) : ℝ := (-1 : ℝ) ^ (m + 1) * K (m + 1) / (m + 1).factorial

lemma S_recurrence (m : ℕ) : S (m + 2) = (4*m + 10 : ℝ) * S (m + 1) + S m := by
  unfold S
  have hK := K_recurrence (m + 3) (by omega : 2 ≤ m + 3)
  -- K(m+3) relation, now algebra with factorials/signs
  rw [hK]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+1)), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+2)), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+3))]
  rw [show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
  ring_nf


lemma K_zero : K 0 = Real.exp 1 - 1 := by
  dsimp [K]
  simpa using intervalIntegral.integral_exp 0 1

lemma K_one : K 1 = 3 - Real.exp 1 := by
  dsimp [K]
  have hder : deriv (fun x : ℝ => Real.exp x * (-x^2 + 3*x - 3)) = fun x => Real.exp x * (x * (1 - x)) := by
    funext x
    change deriv (((fun x : ℝ => Real.exp x) * (fun x : ℝ => -x^2 + 3*x - 3))) x = _
    rw [deriv_mul (c := fun x : ℝ => Real.exp x) (d := fun x : ℝ => -x^2 + 3*x - 3)]
    · rw [Real.deriv_exp]
      have hp : deriv (fun x : ℝ => -x^2 + 3*x - 3) x = -2*x + 3 := by
        have h1 : HasDerivAt (fun x : ℝ => -(x^2)) (-(2*x)) x := by
          convert ((hasDerivAt_id x).pow 2).neg using 1
          · simp
        have h2 : HasDerivAt (fun x : ℝ => 3*x) 3 x := by
          convert ((hasDerivAt_const x (3:ℝ)).mul (hasDerivAt_id x)) using 1 <;> ring
        have h3 : HasDerivAt (fun x : ℝ => -x^2 + 3*x - 3) (-2*x + 3) x := by
          convert (h1.add h2).sub (hasDerivAt_const x (3:ℝ)) using 1 <;> ring
        exact h3.deriv
      rw [hp]
      ring
    · exact Real.differentiableAt_exp
    · fun_prop
  simp only [pow_one]
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (a := (0:ℝ)) (b := (1:ℝ))
    (fun x : ℝ => Real.exp x * (-x^2 + 3*x - 3)) hder
    (by intro x hx; fun_prop)
    (by fun_prop)
  rw [hftc]
  norm_num
  ring

lemma K_two : K 2 = 14 * Real.exp 1 - 38 := by
  have h := K_recurrence 2 (by norm_num)
  norm_num [K_zero, K_one] at h
  linarith

lemma S_zero : S 0 = Real.exp 1 - 3 := by
  norm_num [S, K_one]

lemma S_one : S 1 = 7 * Real.exp 1 - 19 := by
  norm_num [S, K_two]
  ring


lemma K_nonneg (r : ℕ) : 0 ≤ K r := by
  dsimp [K]
  apply intervalIntegral.integral_nonneg
  · norm_num
  · intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have ht0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
    exact mul_nonneg (Real.exp_pos x).le (pow_nonneg ht0 r)

lemma K_le_exp (r : ℕ) : K r ≤ Real.exp 1 := by
  dsimp [K]
  have hmono : (∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ r) ≤ ∫ x in (0:ℝ)..1, Real.exp 1 := by
    apply intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := (1:ℝ)) (μ := volume)
    · norm_num
    · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have ht0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
      have ht1 : x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg (x-1)]
      have htpow : (x * (1 - x)) ^ r ≤ 1 := by
        exact pow_le_one₀ ht0 ht1
      have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
      simpa using mul_le_mul hexp htpow (pow_nonneg ht0 r) (Real.exp_pos 1).le
  have hconst : (∫ x in (0:ℝ)..1, Real.exp 1) = Real.exp 1 := by simp
  simpa [hconst] using hmono

lemma S_tendsto_zero : Filter.Tendsto S Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ m, |S m| ≤ Real.exp 1 * (((m+1).factorial : ℝ)⁻¹) := by
    intro m
    have hK0 := K_nonneg (m+1)
    have hK1 := K_le_exp (m+1)
    unfold S
    have hfacpos : 0 < ((m+1).factorial : ℝ) := by positivity
    rw [abs_div, abs_mul, abs_pow]
    norm_num
    rw [abs_of_nonneg hK0]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hK1 (inv_nonneg.mpr hfacpos.le)
  refine squeeze_zero (fun m => ?_) hbound ?_
  · exact abs_nonneg (S m)
  · have ht : Filter.Tendsto (fun m : ℕ => Real.exp 1 * (((m+1).factorial : ℝ)⁻¹)) Filter.atTop (nhds (Real.exp 1 * 0)) := by
      apply Filter.Tendsto.const_mul
      have hfacNat : Filter.Tendsto (fun m : ℕ => (m + 1).factorial) Filter.atTop Filter.atTop :=
        factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
      have hfacReal : Filter.Tendsto (fun m : ℕ => ((m + 1).factorial : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp hfacNat
      exact tendsto_inv_atTop_zero.comp hfacReal
    simpa using ht
