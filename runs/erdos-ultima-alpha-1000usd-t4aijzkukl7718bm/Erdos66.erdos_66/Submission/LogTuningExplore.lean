import FormalConjecturesUtil

/-! Logarithmic tuning of finite cyclic periods. No infinite integer set is
constructed in this file. -/
namespace Erdos66LogTuning
open Filter
open scoped Topology

noncomputable def rootScale (d : ℝ) (p : ℕ) : ℝ := Real.sqrt (Real.log p / d)
noncomputable def thickness (d : ℝ) (p : ℕ) : ℕ := ⌊rootScale d p⌋₊

lemma log_nat_atTop : Tendsto (fun p : ℕ ↦ Real.log p) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma rootScale_atTop {d : ℝ} (hd : 0 < d) : Tendsto (rootScale d) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (log_nat_atTop.atTop_div_const hd)

lemma thickness_atTop {d : ℝ} (hd : 0 < d) : Tendsto (thickness d) atTop atTop :=
  tendsto_nat_floor_atTop.comp (rootScale_atTop hd)

lemma thickness_root_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ (thickness d p : ℝ) / rootScale d p) atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp (rootScale_atTop hd)

lemma rootScale_sq {d : ℝ} (hd : 0 < d) {p : ℕ} (hp : 1 ≤ p) :
    rootScale d p ^ 2 = Real.log p / d := by
  exact Real.sq_sqrt (div_nonneg (Real.log_natCast_nonneg p) hd.le)

lemma rootScale_log_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ rootScale d p / Real.log p) atTop (𝓝 0) := by
  have hh := ((rootScale_atTop hd).atTop_mul_const hd).const_div_atTop 1
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  have hx : rootScale d p ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos (by exact_mod_cast hp)) hd)
  have hs := rootScale_sq hd (show 1 ≤ p by omega)
  have hsm : rootScale d p ^ 2 * d = Real.log p := (eq_div_iff hd.ne').mp hs
  field_simp
  nlinarith

lemma thickness_log_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ (thickness d p : ℝ) / Real.log p) atTop (𝓝 0) := by
  have hh := (thickness_root_ratio hd).mul (rootScale_log_ratio hd)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hx : rootScale d p ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos (by exact_mod_cast hp)) hd)
  field_simp

lemma log_thickness_log_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ Real.log (thickness d p) / Real.log p) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (thickness_log_ratio hd)
  · filter_upwards [(thickness_atTop hd).eventually (eventually_ge_atTop 1), eventually_ge_atTop 2] with p hK hp
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · filter_upwards [(thickness_atTop hd).eventually (eventually_ge_atTop 1), eventually_ge_atTop 2] with p hK hp
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg _)
    have hKpos : (0 : ℝ) < thickness d p := by exact_mod_cast hK
    linarith [Real.log_le_sub_one_of_pos hKpos]

lemma tuned_mean_logp {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ (2 * d) * (thickness d p : ℝ) ^ 2 / Real.log p) atTop (𝓝 2) := by
  have hh := ((thickness_root_ratio hd).pow 2).const_mul 2
  norm_num only [one_pow, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hx : rootScale d p ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos (by exact_mod_cast hp)) hd)
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  have hs := rootScale_sq hd (show 1 ≤ p by omega)
  rw [div_pow, hs]
  field_simp

lemma scaled_period_log_ratio {d : ℝ} (hd : 0 < d) (j : ℕ) (hj : 0 < j) :
    Tendsto (fun p : ℕ ↦ Real.log (j * (p * thickness d p) ^ 2 : ℕ) / Real.log p)
      atTop (𝓝 2) := by
  have hjlim := log_nat_atTop.const_div_atTop (Real.log (j : ℝ))
  have hh := hjlim.add (((log_thickness_log_ratio hd).const_add 1).const_mul 2)
  norm_num only [add_zero, mul_one, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,
    (thickness_atTop hd).eventually (eventually_ge_atTop 1)] with p hp hK
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hK0 : (thickness d p : ℝ) ≠ 0 := by exact_mod_cast (show thickness d p ≠ 0 by omega)
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  push_cast
  rw [Real.log_mul hj0 (pow_ne_zero _ (mul_ne_zero hp0 hK0)), Real.log_pow,
    Real.log_mul hp0 hK0]
  field_simp
  ring

/-- The main count is asymptotic to the logarithm throughout any fixed
multiplicative range of periods. -/
theorem tuned_mean_scaled_log {d : ℝ} (hd : 0 < d) (j : ℕ) (hj : 0 < j) :
    Tendsto (fun p : ℕ ↦ (2 * d) * (thickness d p : ℝ) ^ 2 /
      Real.log (j * (p * thickness d p) ^ 2 : ℕ)) atTop (𝓝 1) := by
  have hh := (tuned_mean_logp hd).div (scaled_period_log_ratio hd j hj) (by norm_num : (2 : ℝ) ≠ 0)
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  exact div_div_div_cancel_right₀ hl _ _

lemma tuned_mean_uniform {d : ℝ} (hd : 0 < d) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, ∀ n : ℕ,
      (p * thickness d p) ^ 2 ≤ n → n ≤ (L + 1) * (p * thickness d p) ^ 2 →
      |(2 * d) * (thickness d p : ℝ) ^ 2 / Real.log n - 1| < ε := by
  have h₁ := Metric.tendsto_atTop.mp (tuned_mean_scaled_log hd 1 (by omega)) ε hε
  have h₂ := Metric.tendsto_atTop.mp (tuned_mean_scaled_log hd (L + 1) (by omega)) ε hε
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop N₂, eventually_ge_atTop 2,
    (thickness_atTop hd).eventually (eventually_ge_atTop 1)] with p hp₁ hp₂ hp hK
  intro n hnlo hnhi
  have hlow := hN₁ p hp₁
  have hhigh := hN₂ p hp₂
  simp only [one_mul, Real.dist_eq] at hlow hhigh
  have hpK : 2 ≤ p * thickness d p := by nlinarith
  have hM : 1 < (p * thickness d p) ^ 2 := by nlinarith
  have hN : 1 < n := by omega
  have hU : 1 < (L + 1) * (p * thickness d p) ^ 2 := by omega
  have hlogM : 0 < Real.log ((p * thickness d p) ^ 2 : ℕ) := Real.log_pos (by exact_mod_cast hM)
  have hlogN : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hloglo : Real.log ((p * thickness d p) ^ 2 : ℕ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (show 0 < (p * thickness d p) ^ 2 by omega)) (by exact_mod_cast hnlo)
  have hloghi : Real.log (n : ℝ) ≤ Real.log ((L + 1) * (p * thickness d p) ^ 2 : ℕ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnhi)
  have hμ : 0 ≤ (2 * d) * (thickness d p : ℝ) ^ 2 := by positivity
  have hrlo := div_le_div_of_nonneg_left hμ hlogN hloghi
  have hrhi := div_le_div_of_nonneg_left hμ hlogM hloglo
  rw [abs_lt] at hlow hhigh ⊢
  constructor <;> linarith

end Erdos66LogTuning
