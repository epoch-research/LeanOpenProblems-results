import Submission.ArbitraryExposureBudget

/-! Unconditional void exponents arbitrarily close to 1/2 at linear length
and to 1 at quadratic length. No endpoint or nonlinear correlation bound
is asserted. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma general_exposure_core_cost (D t a c : ℕ) (ht : 0 < t)
    (hac : c+2 ≤ a) (hlarge : 400*(a+3)*(D+2) ≤ t) :
    ((D : ℝ)+2)*(3+(a : ℝ)*log t) ≤ (t : ℝ)^(a-c)/400 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog := log_le_sub_one_of_pos ht0
  have hl : (400 : ℝ)*((a : ℝ)+3)*((D : ℝ)+2) ≤ t := by exact_mod_cast hlarge
  have hp : (t : ℝ)^2 ≤ (t : ℝ)^(a-c) := pow_le_pow_right₀ ht1 (by omega)
  have hh := mul_le_mul_of_nonneg_left
    (show 3+(a : ℝ)*log (t : ℝ) ≤ ((a : ℝ)+3)*t by
      nlinarith only [hlog,ht1,Nat.cast_nonneg (α := ℝ) a])
    (show 0 ≤ (D : ℝ)+2 by positivity)
  have hs := mul_le_mul_of_nonneg_right hl ht0.le
  nlinarith only [hh,hs,hp]

lemma general_exposure_core_envelope (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hSP : S ⊆ P)
    (k t D a c : ℕ) (ht : 0 < t) (hca : c ≤ a)
    (hScard : S.card ≤ D*t^c+1)
    (htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 199/200)
    (hcost : ((D : ℝ)+2)*(3+(a : ℝ)*log t) ≤ (t : ℝ)^(a-c)/400)
    (hb : IsJacobsthalBound (t^a-1) k) :
    coveredFraction P k ≤ exp (-(t : ℝ)^a/400) := by
  have hh := coveredFraction_le_general_core P S hP hSP k (t^a) (by positivity)
    hb (199/200) (by norm_num) htail
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hpowc : (1 : ℝ) ≤ (t : ℝ)^c := one_le_pow₀ ht1
  have hpowa : (1 : ℝ) ≤ (t : ℝ)^a := one_le_pow₀ ht1
  have hsmall : log (1+(t^a : ℕ)/(199/200 : ℝ)) ≤ 3+(a : ℝ)*log (t : ℝ) := by
    have hl := log_le_log (by positivity : (0 : ℝ) < 1+(t^a : ℕ)/(199/200 : ℝ))
      (show 1+(t^a : ℕ)/(199/200 : ℝ) ≤ 3*(t : ℝ)^a by push_cast; nlinarith only [hpowa])
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'), log_pow] at hl
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hcount : (S.card : ℝ)+1 ≤ ((D : ℝ)+2)*(t : ℝ)^c := by
    have hc : (S.card : ℝ) ≤ (D : ℝ)*(t : ℝ)^c+1 := by exact_mod_cast hScard
    nlinarith
  have hmain := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 199/200)
  have hmain' : log (199/200 : ℝ) ≤ -1/200 := by norm_num at hmain ⊢; linarith
  have hover : (S.card : ℝ)*log (1+(t^a : ℕ)/(199/200 : ℝ))+1+log (t^a : ℕ)/2 ≤
      (t : ℝ)^a/400 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg S.card)
    have h2 := mul_le_mul_of_nonneg_right hcount
      (show 0 ≤ 3+(a : ℝ)*log (t : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcost (show 0 ≤ (t : ℝ)^c by positivity)
    rw [Nat.cast_pow, log_pow]
    have he : ((t : ℝ)^(a-c)/400)*(t : ℝ)^c = (t : ℝ)^a/400 := by
      rw [div_mul_eq_mul_div,← pow_add,Nat.sub_add_cancel hca]
    push_cast at h1
    rw [he] at h3
    have halog : 0 ≤ (a : ℝ)*log (t : ℝ) := mul_nonneg (Nat.cast_nonneg a) hlog
    nlinarith only [h1,h2,h3,halog]
  have hneg := mul_le_mul_of_nonneg_left hmain' (show 0 ≤ (t : ℝ)^a by positivity)
  apply hh.trans
  apply exp_le_exp.mpr
  push_cast at hover ⊢
  linarith only [hover,hneg]

lemma parameterized_exposure_core_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k t D j : ℕ) (ht : 0 < t) (hcard : P.card ≤ t^(80*(j+1)))
    (hD : 1024 ≤ D) (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hcost : ((D : ℝ)+2)*(3+(40*j+39 : ℕ)*log t) ≤
      (t : ℝ)^((40*j+39)-(30*(j+1)))/400)
    (hb : IsJacobsthalBound (t^(40*j+39)-1) k) :
    coveredFraction P k ≤ exp (-(t : ℝ)^(40*j+39)/400) := by
  let S := P.filter (fun p => p ≤ D*t^(30*(j+1)))
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D*t^(30*(j+1))+1 := by
    have hs : S ⊆ range (D*t^(30*(j+1))+1) := by
      intro p hp
      exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
    simpa only [card_range] using card_le_card hs
  have htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 199/200 := by
    have he : P \ S = P.filter (fun p => D*t^(30*(j+1)) < p) := by
      ext p
      simp only [S, mem_filter]
      by_cases hp : p ∈ P <;> simp [hp]
    rw [he]
    have hc : P.card ≤ (t^(j+1))^80 := by
      rw [← pow_mul,Nat.mul_comm (j+1) 80]
      exact hcard
    have hh := WeightedMertens.tail_three_eighths P hP (t^(j+1)) D
      (Nat.pow_pos ht) hD hlogD hc
    rw [← pow_mul,Nat.mul_comm (j+1) 30] at hh
    simpa only [one_div] using hh
  exact general_exposure_core_envelope P S hP hSP k t D (40*j+39) (30*(j+1))
    ht (by omega) hScard htail hcost hb

/-- A sequence of linear-length exponents increasing to one half. -/
theorem eventually_parameterized_linear_void_of_constants (D j : ℕ)
    (hD : 1024 ≤ D)
    (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ)) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^((40*(j : ℝ)+39)/(80*(j+1)))/400)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_subsquare_exposure_budget (40*j+39) (80*(j+1)) (by omega) (by omega))
  let T := max (max (400*((40*j+39)+3)*(D+2)) N) 1
  filter_upwards [eventually_ge_atTop (T^(80*(j+1)))] with k hk
  intro P hP hPk
  have hT : 0 < T := by dsimp [T]; omega
  have hb0 : 0 < 80*(j+1) := by omega
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k (80*(j+1)) hkpos hb0
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left hb0.ne').mp (hk.trans hkt)
  have hDt : 400*((40*j+39)+3)*(D+2) ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hTt)
  have hNt : N ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans hTt)
  have hh := parameterized_exposure_core_envelope P hP k t D j ht (hPk.trans hkt) hD hlogD
    (general_exposure_core_cost D t (40*j+39) (30*(j+1)) ht (by omega) hDt) (hN t hNt k hroot)
  have hp : (k : ℝ)^((40*(j : ℝ)+39)/(80*(j+1))) ≤ (t : ℝ)^(40*j+39) := by
    have he := rpow_le_rpow (Nat.cast_nonneg k)
      (show (k : ℝ) ≤ (t : ℝ)^(80*(j+1)) by exact_mod_cast hkt)
      (show 0 ≤ (40*(j : ℝ)+39)/(80*(j+1)) by positivity)
    rw [← rpow_natCast (t : ℝ) (80*(j+1)), ← rpow_mul (Nat.cast_nonneg t)] at he
    have heq : ((80*(j+1) : ℕ) : ℝ)*((40*(j : ℝ)+39)/(80*(j+1))) = (40*j+39 : ℕ) := by
      push_cast
      field_simp
    rw [heq,rpow_natCast] at he
    exact he
  exact hh.trans (exp_le_exp.mpr (by linarith only [hp]))

/-- The constants are uniform in the prime set; the threshold depends on
j. In particular this theorem asserts no uniformity at the limit j=infinity. -/
theorem eventually_parameterized_linear_void (j : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^((40*(j : ℝ)+39)/(80*(j+1)))/400)) :=
  eventually_parameterized_linear_void_of_constants FiniteSelberg.thirteenSixteenthCutoffScale j
    ((by norm_num : 1024 ≤ 65536).trans FiniteSelberg.thirteenSixteenthCutoffScale_ge)
    exposureCutoffScale_log

lemma exists_subhalf_parameter (σ : ℝ) (hσ : σ < 1/2) :
    ∃ j : ℕ, σ ≤ (40*(j : ℝ)+39)/(80*(j+1)) := by
  have hδ : 0 < 1/2-σ := by linarith
  obtain ⟨j,hj⟩ := exists_nat_gt (1/(1/2-σ))
  have hj' : 1 < (j : ℝ)*(1/2-σ) := (div_lt_iff₀ hδ).mp hj
  refine ⟨j,(le_div_iff₀ (by positivity : (0 : ℝ) < 80*(j+1))).mpr ?_⟩
  nlinarith only [hj',hδ]

/-- Every fixed linear-length exponent strictly below one half. -/
theorem eventually_subhalf_linear_void (σ : ℝ) (hσ : σ < 1/2) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^σ/400)) := by
  obtain ⟨j,hj⟩ := exists_subhalf_parameter σ hσ
  filter_upwards [eventually_parameterized_linear_void j,eventually_ge_atTop 1] with k hk hk1
  intro P hP hPk
  apply (hk P hP hPk).trans
  have hp := rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ k by exact_mod_cast hk1) hj
  exact exp_le_exp.mpr (by linarith only [hp])

/-- Every fixed quadratic-length exponent strictly below one. This remains
short of the k*log k scale needed by the existing phase-entropy argument. -/
theorem eventually_subone_quadratic_void (σ : ℝ) (hσ : σ < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P (k^2) ≤ exp (-((k : ℝ)^σ/400)) := by
  have hs := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually
    (eventually_subhalf_linear_void (σ/2) (by linarith))
  filter_upwards [hs] with k hk
  intro P hP hPk
  have hh := hk P hP (hPk.trans (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) k))
  simpa only [Nat.cast_pow, ← rpow_natCast (k : ℝ) 2,
    ← rpow_mul (Nat.cast_nonneg k),Nat.cast_ofNat,mul_div_cancel₀ σ (by norm_num : (2 : ℝ) ≠ 0)] using hh

#print axioms eventually_subhalf_linear_void
#print axioms eventually_subone_quadratic_void
end Erdos970.GapAverages
