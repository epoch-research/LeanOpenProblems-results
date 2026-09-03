import Submission.QuadraticPhaseResonanceExplore

/-! Polynomial-sized representation peaks from very good square-unit
rational approximations of a quadratic phase. -/
namespace Erdos66QuadraticPhasePeaks
open Filter AdditiveCombinatorics Erdos66QuadraticPhaseResonance
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def resonanceSize (p : ℕ) : ℕ :=
  ⌊Real.sqrt (Real.sqrt (p:ℝ))/4⌋₊

lemma resonanceSize_sq_bound (p : ℕ) :
    (resonanceSize p:ℝ)^2 ≤ Real.sqrt (p:ℝ)/16 := by
  have hb : (resonanceSize p:ℝ) ≤ Real.sqrt (Real.sqrt (p:ℝ))/4 :=
    Nat.floor_le (by positivity)
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _) hb 2
  rw [div_pow,Real.sq_sqrt (Real.sqrt_nonneg _)] at hh
  norm_num at hh ⊢
  exact hh

lemma resonanceSize_sq_lt {p : ℕ} (hp : 16 ≤ p) : (resonanceSize p)^2 < p := by
  have hpR : (16:ℝ) ≤ p := by exact_mod_cast hp
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hroot : 4 ≤ Real.sqrt (p:ℝ) := by
    have hh := Real.sqrt_le_sqrt hpR
    norm_num at hh
    exact hh
  have hb := resonanceSize_sq_bound p
  have hmR : (resonanceSize p:ℝ)^2 < (p:ℝ) := by nlinarith
  exact_mod_cast hmR

lemma resonance_budget {p n : ℕ} (hp : 16 ≤ p) (hn : n ≤ p) :
    (1/(p:ℝ)^3)*(p:ℝ)^2+(resonanceSize p:ℝ)^2/(p:ℝ) ≤
      1/Real.sqrt ((n:ℝ)+1) := by
  have hpR : (16:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hs0 := Real.sqrt_nonneg (p:ℝ)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hroot : 4 ≤ Real.sqrt (p:ℝ) := by
    have hh := Real.sqrt_le_sqrt hpR
    norm_num at hh
    exact hh
  have hnR : (n:ℝ) ≤ p := by exact_mod_cast hn
  have ht : Real.sqrt ((n:ℝ)+1) ≤ 2*Real.sqrt (p:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hm := resonanceSize_sq_bound p
  have hb : 1+(resonanceSize p:ℝ)^2 ≤ Real.sqrt (p:ℝ)/2 := by nlinarith
  have hts : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hmul := mul_le_mul hb ht (Real.sqrt_nonneg _) (by positivity)
  have hbound : (1+(resonanceSize p:ℝ)^2)*Real.sqrt ((n:ℝ)+1) ≤ (p:ℝ) := by
    nlinarith
  have hq : (1+(resonanceSize p:ℝ)^2)/(p:ℝ) ≤ 1/Real.sqrt ((n:ℝ)+1) := by
    apply (div_le_div_iff₀ hp0 hts).mpr
    simpa only [one_mul] using hbound
  convert hq using 1
  field_simp

/-- The lower window hypothesis also covers logarithmic square-root windows. -/
theorem cubic_approximation_peak (α : ℝ) (w : ℕ → ℝ) (p a : ℕ)
    (hp : 16 ≤ p) (u : (ZMod p)ˣ) (hu : (a:ZMod p)*(u:ZMod p)^2=1)
    (happrox : |α-(a:ℝ)/p| ≤ 1/(p:ℝ)^3)
    (hw : ∀ n : ℕ, 1/Real.sqrt ((n:ℝ)+1) ≤ w n) :
    resonanceSize p ≤ sumRep (phaseSet α w) p := by
  exact finite_resonance α w p a (resonanceSize p) (by omega)
    (resonanceSize_sq_lt hp) u hu (1/(p:ℝ)^3) (by positivity) happrox
    (fun n hn ↦ (resonance_budget hp hn).trans (hw n))

lemma log_div_fourth_root_zero :
    Tendsto (fun p : ℕ ↦ Real.log (p:ℝ)/Real.sqrt (Real.sqrt (p:ℝ)))
      atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/4)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hh using 1
  funext p
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg (α := ℝ) p)]
  norm_num

lemma fourth_root_atTop :
    Tendsto (fun p : ℕ ↦ Real.sqrt (Real.sqrt (p:ℝ))) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))

lemma resonanceSize_log_atTop :
    Tendsto (fun p : ℕ ↦ (resonanceSize p:ℝ)/Real.log p) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C := max 0 B+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCB : B < C := by dsimp [C]; linarith [le_max_right 0 B]
  have hsmall := log_div_fourth_root_zero.eventually_lt_const
    (show (0:ℝ)<1/(8*C) by positivity)
  have hlarge := fourth_root_atTop.eventually_ge_atTop 8
  filter_upwards [hsmall,hlarge,eventually_ge_atTop 2] with p hs hl hp
  have hpR : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hroot : 0 < Real.sqrt (Real.sqrt (p:ℝ)) := by linarith
  have hsc := (div_lt_div_iff₀ hroot (show (0:ℝ)<8*C by positivity)).mp hs
  have hfloor := Nat.sub_one_lt_floor (Real.sqrt (Real.sqrt (p:ℝ))/4)
  change Real.sqrt (Real.sqrt (p:ℝ))/4-1 < (resonanceSize p:ℝ) at hfloor
  apply (le_div_iff₀ hlog).mpr
  have hBc := mul_le_mul_of_nonneg_right hCB.le hlog.le
  nlinarith

/-- Infinitely many cubic-accuracy square-unit approximations force
arbitrarily large normalized representation peaks for this particular set. -/
theorem unbounded_peaks_of_approximations (α : ℝ) (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1/Real.sqrt ((n:ℝ)+1) ≤ w n)
    (happrox : ∃ᶠ p : ℕ in atTop, ∃ a : ℕ, ∃ u : (ZMod p)ˣ,
      (a:ZMod p)*(u:ZMod p)^2=1 ∧ |α-(a:ℝ)/p| ≤ 1/(p:ℝ)^3) :
    ∀ B : ℝ, ∃ᶠ p : ℕ in atTop,
      B < (sumRep (phaseSet α w) p:ℝ)/Real.log p := by
  intro B
  have hb := resonanceSize_log_atTop.eventually_gt_atTop B
  apply ((hb.and (eventually_ge_atTop 16)).and_frequently happrox).mono
  rintro p ⟨⟨hBp,hp⟩,a,u,hu,ha⟩
  have hpeak := cubic_approximation_peak α w p a hp u hu ha hw
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (show 1<p by omega))
  exact hBp.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hpeak) hlog.le)

theorem no_finite_limit_of_approximations (α : ℝ) (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1/Real.sqrt ((n:ℝ)+1) ≤ w n)
    (happrox : ∃ᶠ p : ℕ in atTop, ∃ a : ℕ, ∃ u : (ZMod p)ˣ,
      (a:ZMod p)*(u:ZMod p)^2=1 ∧ |α-(a:ℝ)/p| ≤ 1/(p:ℝ)^3) (c : ℝ) :
    ¬ Tendsto (fun p ↦ (sumRep (phaseSet α w) p:ℝ)/Real.log p) atTop (𝓝 c) := by
  intro h
  have he := h.eventually_lt_const (lt_add_one c)
  have hf := unbounded_peaks_of_approximations α w hw happrox (c+1)
  obtain ⟨p,hp,hp'⟩ := (he.and_frequently hf).exists
  linarith

noncomputable def logWindow (n : ℕ) : ℝ :=
  Real.sqrt (1+Real.log ((n:ℝ)+1))/Real.sqrt ((n:ℝ)+1)

lemma logWindow_lower (n : ℕ) : 1/Real.sqrt ((n:ℝ)+1) ≤ logWindow n := by
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hl : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hh := Real.sqrt_le_sqrt (show (1:ℝ)≤1+Real.log ((n:ℝ)+1) by linarith)
  simpa only [Real.sqrt_one] using hh

end Erdos66QuadraticPhasePeaks
