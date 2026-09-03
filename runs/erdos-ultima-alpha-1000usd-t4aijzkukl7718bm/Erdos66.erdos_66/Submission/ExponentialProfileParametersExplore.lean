import Submission.RandomConstantProfileExplore

/-! Quantitative choices for the finite random constant-profile construction. -/
namespace Erdos66ExponentialProfileParameters
open Filter Erdos66RandomConstantProfile
open scoped Topology
set_option maxHeartbeats 800000

noncomputable def start (μ ε : ℝ) : ℕ := ⌈64 * (⌈μ⌉₊ : ℝ) ^ 2 / ε ^ 2⌉₊
noncomputable def cutoff (μ k : ℝ) : ℕ := ⌊Real.exp (k * μ)⌋₊

lemma start_condition (μ ε : ℝ) (hε : 0 < ε) :
    64 * (⌈μ⌉₊ : ℝ) ^ 2 ≤ ε ^ 2 * ((start μ ε : ℝ) + 1) := by
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp
    (Nat.le_ceil (64 * (⌈μ⌉₊ : ℝ) ^ 2 / ε ^ 2))
  dsimp [start]
  nlinarith [sq_nonneg ε]

lemma start_upper (μ ε : ℝ) (hμ : 1 ≤ μ) (hε : 0 < ε) :
    (start μ ε : ℝ) + 3 ≤ (256 / ε ^ 2 + 4) * μ ^ 2 := by
  have hs := Nat.ceil_lt_add_one (show 0 ≤ μ by linarith)
  have hs0 : (0 : ℝ) ≤ ⌈μ⌉₊ := Nat.cast_nonneg _
  have hq := Nat.ceil_lt_add_one (show 0 ≤ 64 * (⌈μ⌉₊ : ℝ) ^ 2 / ε ^ 2 by positivity)
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hq' := (lt_div_iff₀ he).mp (show ((start μ ε : ℝ) - 1) < 64 * (⌈μ⌉₊ : ℝ) ^ 2 / ε ^ 2 by
    dsimp [start]; linarith)
  have hs2 : (⌈μ⌉₊ : ℝ) ^ 2 ≤ 4 * μ ^ 2 := by nlinarith
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith
  apply (mul_le_mul_iff_right₀ he).mp
  have hid : ((256 / ε ^ 2 + 4) * μ ^ 2) * ε ^ 2 = (256 + 4 * ε ^ 2) * μ ^ 2 := by
    field_simp
  rw [mul_comm (ε ^ 2) ((256 / ε ^ 2 + 4) * μ ^ 2), hid]
  nlinarith [mul_le_mul_of_nonneg_left hμ2 (show 0 ≤ 4 * ε ^ 2 by positivity)]

lemma cutoff_lower (μ k : ℝ) (hbig : 2 ≤ Real.exp (k * μ / 2)) :
    Real.exp (k * μ / 2) ≤ (cutoff μ k : ℝ) := by
  have hf := Nat.lt_floor_add_one (Real.exp (k * μ))
  have he : Real.exp (k * μ) = Real.exp (k * μ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  dsimp [cutoff]
  rw [he] at hf ⊢
  nlinarith

lemma cutoff_small (μ ε k : ℝ) (hμ : 0 ≤ μ) (hk : 0 < k) (hεk : 256 * k ≤ ε ^ 2)
    (hdecay : 6 * Real.exp (-k * μ) < 1) :
    2 * (2 * (cutoff μ k : ℝ) + 1) * Real.exp (-ε ^ 2 * (μ + 1) / 128) < 1 := by
  have hf := Nat.floor_le (Real.exp_pos (k * μ)).le
  have hone := Real.one_le_exp (mul_nonneg hk.le hμ)
  have hpre : 2 * (2 * (cutoff μ k : ℝ) + 1) ≤ 6 * Real.exp (k * μ) := by
    dsimp [cutoff]; linarith
  have hex : -ε ^ 2 * (μ + 1) / 128 ≤ -2 * k * μ := by
    have hh := mul_le_mul_of_nonneg_right hεk (show 0 ≤ μ + 1 by positivity)
    nlinarith
  have hh := mul_le_mul hpre (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le (by positivity)
  have he : 6 * Real.exp (k * μ) * Real.exp (-2 * k * μ) = 6 * Real.exp (-k * μ) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hh
  exact hh.trans_lt hdecay

/-- All the profile and concentration parameters can be chosen by explicit
ceilings and floors. In particular, the starting point is polynomial in μ
and the terminal point is exponential in μ. -/
theorem eventually_parameters (ε k : ℝ) (hε : 0 < ε) (hk : 0 < k) (hεk : 256 * k ≤ ε ^ 2) :
    ∀ᶠ μ : ℝ in atTop,
      1 ≤ μ ∧ 4 ≤ ε * μ ∧
      (start μ ε : ℝ) + 3 ≤ Real.exp (k * μ / 4) ∧
      Real.exp (k * μ / 2) ≤ (cutoff μ k : ℝ) ∧
      2 * (2 * (cutoff μ k : ℝ) + 1) * Real.exp (-ε ^ 2 * (μ + 1) / 128) < 1 := by
  let C : ℝ := 256 / ε ^ 2 + 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hpoly := (isLittleO_pow_exp_pos_mul_atTop 2 (show 0 < k / 4 by positivity)).bound
    (show 0 < 1 / C by positivity)
  have hexp : Tendsto (fun μ : ℝ ↦ Real.exp (k * μ / 2)) atTop atTop := by
    convert Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (show 0 < k / 2 by positivity)) using 1
    ext μ; dsimp only [id, Function.comp_def]; congr 1; ring
  have hdecay : Tendsto (fun μ : ℝ ↦ 6 * Real.exp (-k * μ)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hk))
    convert hh.const_mul 6 using 1 <;> simp [neg_mul]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.const_mul_atTop hε).eventually_ge_atTop 4, hpoly,
    hexp.eventually_ge_atTop 2, hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with μ hμ hlarge hpoly hexp hdecay
  have hp : C * μ ^ 2 ≤ Real.exp (k * μ / 4) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg μ), abs_of_pos (Real.exp_pos _)] at hpoly
    have hh := (le_div_iff₀ hC).mp (show μ ^ 2 ≤ Real.exp ((k / 4) * μ) / C by
      simpa only [one_div_mul_eq_div] using hpoly)
    convert hh using 1 <;> ring
  exact ⟨hμ, hlarge, (start_upper μ ε hμ hε).trans hp, cutoff_lower μ k hexp,
    cutoff_small μ ε k (by linarith) hk hεk hdecay⟩

end Erdos66ExponentialProfileParameters
