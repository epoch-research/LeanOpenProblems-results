import Submission.SparseGrowthCostsExplore

/-! Every fixed superquadratic separation of exceptional targets makes the
weighted reciprocal-square-root repair series summable. -/
namespace Erdos66SuperquadraticCosts
open Filter Erdos66ClippedRepair Erdos66SparseGrowthCosts
open scoped Topology Classical
set_option maxHeartbeats 1600000

lemma logScale_pow_div_rpow_limit (m : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (logScale n)^m / ((n : ℝ)+1)^a) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := ((isLittleO_log_rpow_rpow_atTop (m : ℝ) ha).tendsto_div_nhds_zero).comp hnat
  simp only [Real.rpow_natCast] at hh
  refine squeeze_zero' (Eventually.of_forall (fun n ↦ div_nonneg
    (pow_nonneg (logScale_pos n).le m) (Real.rpow_nonneg (by positivity) a))) ?_
    (by simpa only [Function.comp_def,mul_zero] using hh.const_mul ((2:ℝ)^m))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := pow_le_pow_left₀ (logScale_pos n).le (logScale_le_log_succ hn) m
  have hd := div_le_div_of_nonneg_right hb (Real.rpow_nonneg (show (0:ℝ) ≤ n+1 by positivity) a)
  simpa only [mul_pow,mul_div_assoc] using hd

lemma eventually_logScale_pow_le_rpow (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, (logScale n)^m ≤ ((n : ℝ)+1)^a := by
  filter_upwards [(logScale_pow_div_rpow_limit m a ha).eventually_lt_const
    (show (0:ℝ) < 1 by norm_num)] with n hn
  have hp : 0 < ((n : ℝ)+1)^a := Real.rpow_pos_of_pos (by positivity) a
  exact ((div_lt_iff₀ hp).mp hn).le.trans_eq (one_mul _)

theorem weighted_cost_summable (p : ℝ) (hp : 2 < p) (n : ℕ → ℕ)
    (hg : ∀ᶠ k : ℕ in atTop, ((k : ℝ)+1)^p ≤ n k) :
    Summable (fun k ↦ logScale (n k)*Real.sqrt (logScale (n k))/Real.sqrt ((n k : ℝ)+1)) := by
  let a := (p-2)/(4*p)
  let b := (p+2)/(4*p)
  let s := (p+2)/4
  have hp0 : 0 < p := by linarith
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hb : 0 < b := div_pos (by linarith) (by positivity)
  have hs : 1 < s := by dsimp [s]; linarith
  have hab : a-1/2 = -b := by dsimp [a,b]; field_simp; ring
  have hpb : p*b = s := by dsimp [b,s]; field_simp
  have hn : Tendsto n atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [hg] with k hk
    have hh := Real.self_le_rpow_of_one_le (show (1:ℝ) ≤ k+1 by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      (show (1:ℝ) ≤ p by linarith)
    have hh' : (k:ℝ) ≤ n k := by linarith
    exact_mod_cast hh'
  have hser : Summable (fun k : ℕ ↦ 1/((k : ℝ)+1)^s) := by
    have habs (k : ℕ) : |(k : ℝ)+1| = (k : ℝ)+1 := abs_of_pos (by positivity)
    simpa only [habs] using
      (Real.summable_one_div_nat_add_rpow 1 s).mpr hs
  apply hser.of_norm_bounded_eventually_nat
  filter_upwards [hg,hn.eventually (eventually_logScale_pow_le_rpow 2 a ha),
    (logScale_atTop.comp hn).eventually_ge_atTop 1] with k hk hl hlarge
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  change 1 ≤ logScale (n k) at hlarge
  have hlog0 := (logScale_pos (n k)).le
  have hslog : Real.sqrt (logScale (n k)) ≤ logScale (n k) :=
    Real.sqrt_le_iff.mpr ⟨hlog0,by nlinarith⟩
  have hnum : logScale (n k)*Real.sqrt (logScale (n k)) ≤ ((n k : ℝ)+1)^a := by
    have hh := mul_le_mul_of_nonneg_left hslog hlog0
    nlinarith
  have hnp : (0:ℝ) < (n k : ℝ)+1 := by positivity
  have hkp : (0:ℝ) < (k : ℝ)+1 := by positivity
  have hden : ((k : ℝ)+1)^s ≤ ((n k : ℝ)+1)^b := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hkp.le p)
      (show ((k : ℝ)+1)^p ≤ (n k : ℝ)+1 by linarith) hb.le
    rwa [← Real.rpow_mul hkp.le,hpb] at hh
  calc
    _ ≤ ((n k : ℝ)+1)^a/Real.sqrt ((n k : ℝ)+1) :=
      div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
    _ = 1/((n k : ℝ)+1)^b := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_sub hnp,hab,Real.rpow_neg hnp.le,one_div]
    _ ≤ _ := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hkp s) hden

end Erdos66SuperquadraticCosts
