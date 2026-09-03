import Submission.RepeatedCentersExplore

/-! Polynomial separation of target centers makes the joint-repair cost
series summable, even with logarithmic multiplicities at each target. -/
namespace Erdos66SparseGrowthCosts
open Filter Erdos66RepeatedCenters Erdos66ClippedRepair
open scoped Topology Classical
set_option maxHeartbeats 1600000

lemma logScale_mono : Monotone logScale := by
  intro n m hnm
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 2)

lemma logScale_le_log_succ {n : ℕ} (hn : 1 ≤ n) : logScale n ≤ 2*Real.log ((n : ℝ)+1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := Real.log_le_log (show (0 : ℝ) < n+2 by positivity)
    (show (n : ℝ)+2 ≤ ((n : ℝ)+1)^2 by nlinarith)
  rw [Real.log_pow] at hh
  exact hh

lemma logScale_pow_div_sqrt_limit (p : ℕ) :
    Tendsto (fun n : ℕ ↦ (logScale n)^p / Real.sqrt ((n : ℝ)+1)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := ((isLittleO_log_rpow_rpow_atTop (p : ℝ) (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero).comp hnat
  simp only [Real.rpow_natCast,← Real.sqrt_eq_rpow] at hh
  refine squeeze_zero' (Eventually.of_forall (fun n ↦ div_nonneg
    (pow_nonneg (logScale_pos n).le p) (Real.sqrt_nonneg _))) ?_
    (by simpa only [Function.comp_def,mul_zero] using hh.const_mul ((2:ℝ)^p))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := pow_le_pow_left₀ (logScale_pos n).le (logScale_le_log_succ hn) p
  have hd := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg ((n : ℝ)+1))
  simpa only [mul_pow,mul_div_assoc] using hd

lemma eventually_logScale_pow_le_sqrt (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, (logScale n)^p ≤ Real.sqrt ((n : ℝ)+1) := by
  filter_upwards [(logScale_pow_div_sqrt_limit p).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)] with n hn
  have hs : 0 < Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  exact ((div_lt_iff₀ hs).mp hn).le.trans_eq (one_mul _)

lemma target_tendsto (n : ℕ → ℕ) (hg : ∀ᶠ k : ℕ in atTop, (k+1)^12 ≤ n k) :
    Tendsto n atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [hg] with k hk
  exact (Nat.le_succ k).trans ((Nat.le_pow (by norm_num : 0 < 12)).trans hk)

lemma start_bound (n r : ℕ → ℕ) (hn : Monotone n) (D : ℝ)
    (hr : ∀ k, (r k : ℝ) ≤ D*logScale (n k)) (hD : 0 ≤ D) (k : ℕ) :
    (start r (k+1) : ℝ) ≤ ((k : ℝ)+1)*D*logScale (n k) := by
  have hh : (∑ j ∈ Finset.range (k+1), (r j : ℝ)) ≤
      ∑ _j ∈ Finset.range (k+1), D*logScale (n k) := by
    apply Finset.sum_le_sum
    intro j hj
    apply (hr j).trans
    apply mul_le_mul_of_nonneg_left (logScale_mono (hn (by simpa using hj))) hD
  simpa only [start,Nat.cast_sum,Finset.sum_const,Finset.card_range,Nat.cast_add,
    Nat.cast_one,nsmul_eq_mul,mul_assoc] using hh

lemma root_growth (k N : ℕ) (hg : (k+1)^12 ≤ N) :
    ((k : ℝ)+1)^6 ≤ Real.sqrt ((N : ℝ)+1) ∧
      ((k : ℝ)+1)^3 ≤ Real.sqrt (Real.sqrt ((N : ℝ)+1)) := by
  have hg' : ((k : ℝ)+1)^12 ≤ N := by exact_mod_cast hg
  have hsq : (((k : ℝ)+1)^6)^2 ≤ (N : ℝ)+1 := by nlinarith
  have hroot := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity)] at hroot
  refine ⟨hroot,?_⟩
  have hh : (((k : ℝ)+1)^3)^2 ≤ Real.sqrt ((N : ℝ)+1) := by nlinarith [hroot]
  have hh' := Real.sqrt_le_sqrt hh
  rwa [Real.sqrt_sq (by positivity)] at hh'

lemma cost_bounds (k N r s : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hr : (r : ℝ) ≤ D*logScale N) (hs : (s : ℝ) ≤ ((k : ℝ)+1)*D*logScale N)
    (hg : (k+1)^12 ≤ N) (hl : 1 ≤ logScale N)
    (h5 : (logScale N)^5 ≤ Real.sqrt ((N : ℝ)+1))
    (h4 : (logScale N)^4 ≤ Real.sqrt ((N : ℝ)+1)) :
    (r : ℝ)*(s : ℝ)^4 / ((N : ℝ)+1) ≤ D^5 / ((k : ℝ)+1)^2 ∧
    (r : ℝ)*Real.sqrt (logScale N) / Real.sqrt ((N : ℝ)+1) ≤ D / ((k : ℝ)+1)^3 ∧
    (r : ℝ) / Real.sqrt ((N : ℝ)+1) ≤ D / ((k : ℝ)+1)^3 := by
  have hNp : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have hkp : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have hsqrt : 0 < Real.sqrt ((N : ℝ)+1) := Real.sqrt_pos.mpr hNp
  have hsqrt2 : 0 < Real.sqrt (Real.sqrt ((N : ℝ)+1)) := Real.sqrt_pos.mpr hsqrt
  obtain ⟨hroot,hroot2⟩ := root_growth k N hg
  have hlog0 := (logScale_pos N).le
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) s) hs 4
  have hmul := mul_le_mul hr hpow (pow_nonneg (Nat.cast_nonneg (α := ℝ) s) 4) (by positivity : 0 ≤ D*logScale N)
  have hmain : (r : ℝ)*(s : ℝ)^4 ≤ D^5*((k : ℝ)+1)^4*(logScale N)^5 := by nlinarith [hmul]
  have hlog2 : (logScale N)^2 ≤ Real.sqrt (Real.sqrt ((N : ℝ)+1)) := by
    have hh := Real.sqrt_le_sqrt h4
    have he : (logScale N)^4 = ((logScale N)^2)^2 := by ring
    rw [he,Real.sqrt_sq (sq_nonneg _)] at hh
    exact hh
  have hslog : Real.sqrt (logScale N) ≤ logScale N := Real.sqrt_le_iff.mpr ⟨hlog0,by nlinarith⟩
  have havoid : (r : ℝ)*Real.sqrt (logScale N) ≤ D*(logScale N)^2 := by
    have hh := mul_le_mul hr hslog (Real.sqrt_nonneg _) (mul_nonneg hD hlog0)
    nlinarith
  have hcount : (r : ℝ) ≤ D*(logScale N)^2 := by nlinarith [mul_le_mul_of_nonneg_left (show logScale N ≤ (logScale N)^2 by nlinarith) hD]
  have havbound : D*(logScale N)^2 / Real.sqrt ((N : ℝ)+1) ≤ D / ((k : ℝ)+1)^3 := by
    calc
      _ ≤ D*Real.sqrt (Real.sqrt ((N : ℝ)+1)) / Real.sqrt ((N : ℝ)+1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2 hD) hsqrt.le
      _ = D / Real.sqrt (Real.sqrt ((N : ℝ)+1)) := by rw [mul_div_assoc,Real.sqrt_div_self]; rfl
      _ ≤ _ := div_le_div_of_nonneg_left hD (by positivity) hroot2
  refine ⟨?_,(div_le_div_of_nonneg_right havoid hsqrt.le).trans havbound,
    (div_le_div_of_nonneg_right hcount hsqrt.le).trans havbound⟩
  calc
    _ ≤ D^5*((k : ℝ)+1)^4*(logScale N)^5 / ((N : ℝ)+1) := div_le_div_of_nonneg_right hmain hNp.le
    _ ≤ D^5*((k : ℝ)+1)^4*Real.sqrt ((N : ℝ)+1) / ((N : ℝ)+1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by positivity)) hNp.le
    _ = D^5*((k : ℝ)+1)^4 / Real.sqrt ((N : ℝ)+1) := by rw [mul_div_assoc,Real.sqrt_div_self]; rfl
    _ ≤ D^5*((k : ℝ)+1)^4 / ((k : ℝ)+1)^6 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hroot
    _ = _ := by field_simp <;> ring

lemma shifted_pseries_summable (p : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ ↦ 1 / ((k : ℝ)+1)^p) := by
  have hh : Summable (fun k : ℕ ↦ 1 / (k : ℝ)^p) := Real.summable_one_div_nat_pow.mpr hp
  simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hh

/-- An exponent twelve is a convenient sufficient separation condition; it is
not claimed to be optimal. The target sequence may grow arbitrarily faster. -/
theorem logarithmic_multiplicity_costs (n r : ℕ → ℕ) (hn : Monotone n)
    (hg : ∀ᶠ k : ℕ in atTop, (k+1)^12 ≤ n k) (D : ℝ) (hD : 0 ≤ D)
    (hr : ∀ k, (r k : ℝ) ≤ D*logScale (n k)) :
    Summable (fun k ↦ (r k : ℝ)*(start r (k+1) : ℝ)^4 / ((n k : ℝ)+1)) ∧
    Summable (fun k ↦ (r k : ℝ)*Real.sqrt (logScale (n k)) / Real.sqrt ((n k : ℝ)+1)) ∧
    Summable (fun k ↦ (r k : ℝ) / Real.sqrt ((n k : ℝ)+1)) := by
  have htop := target_tendsto n hg
  have hevent : ∀ᶠ k : ℕ in atTop,
      (r k : ℝ)*(start r (k+1) : ℝ)^4 / ((n k : ℝ)+1) ≤ D^5 / ((k : ℝ)+1)^2 ∧
      (r k : ℝ)*Real.sqrt (logScale (n k)) / Real.sqrt ((n k : ℝ)+1) ≤ D / ((k : ℝ)+1)^3 ∧
      (r k : ℝ) / Real.sqrt ((n k : ℝ)+1) ≤ D / ((k : ℝ)+1)^3 := by
    filter_upwards [hg,htop.eventually (eventually_logScale_pow_le_sqrt 5),
      htop.eventually (eventually_logScale_pow_le_sqrt 4),
      (logScale_atTop.comp htop).eventually_ge_atTop 1] with k hk h5 h4 hl
    exact cost_bounds k (n k) (r k) (start r (k+1)) D hD (hr k) (start_bound n r hn D hr hD k) hk hl h5 h4
  have hs2 : Summable (fun k : ℕ ↦ D^5 / ((k : ℝ)+1)^2) := by
    simpa only [mul_one_div] using (shifted_pseries_summable 2 (by norm_num)).mul_left (D^5)
  have hs3 : Summable (fun k : ℕ ↦ D / ((k : ℝ)+1)^3) := by
    simpa only [mul_one_div] using (shifted_pseries_summable 3 (by norm_num)).mul_left D
  constructor
  · apply hs2.of_norm_bounded_eventually_nat
    filter_upwards [hevent] with k hk
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hk.1
  constructor
  · apply hs3.of_norm_bounded_eventually_nat
    filter_upwards [hevent] with k hk
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hk.2.1
  · apply hs3.of_norm_bounded_eventually_nat
    filter_upwards [hevent] with k hk
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hk.2.2

end Erdos66SparseGrowthCosts
