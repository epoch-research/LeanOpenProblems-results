import Submission.PowerExposureBudget

/-! Sharper unconditional void estimates: exponent49/100 at linear length,
and49/50 at quadratic length. Both are still below the exponent needed to
exclude every phase; this file does NOT settle the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000

lemma near_critical_core_cost (D t : ℕ) (ht : 0 < t) (hlarge : 78800*(D+2) ≤ t) :
    ((D : ℝ)+2)*(3+196*log t) ≤ (t : ℝ)^46/400 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog := log_le_sub_one_of_pos ht0
  have hl : (78800 : ℝ)*((D : ℝ)+2) ≤ t := by exact_mod_cast hlarge
  have hp : (t : ℝ)^2 ≤ (t : ℝ)^46 := pow_le_pow_right₀ ht1 (by omega)
  have hh := mul_le_mul_of_nonneg_left (show 3+196*log (t : ℝ) ≤ 197*t by linarith)
    (show 0 ≤ (D : ℝ)+2 by positivity)
  have hs := mul_le_mul_of_nonneg_right hl ht0.le
  nlinarith only [hh,hs,hp]

lemma near_critical_core_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k t D : ℕ) (ht : 0 < t) (hcard : P.card ≤ t^400)
    (hD : 1024 ≤ D) (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hcost : ((D : ℝ)+2)*(3+196*log t) ≤ (t : ℝ)^46/400)
    (hb : IsJacobsthalBound (t^196-1) k) :
    coveredFraction P k ≤ exp (-(t : ℝ)^196/400) := by
  let S := P.filter (fun p => p ≤ D*t^150)
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D*t^150+1 := by
    have hs : S ⊆ range (D*t^150+1) := by
      intro p hp
      exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
    simpa only [card_range] using card_le_card hs
  have htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 199/200 := by
    have he : P \ S = P.filter (fun p => D*t^150 < p) := by
      ext p
      simp only [S, mem_filter]
      by_cases hp : p ∈ P <;> simp [hp]
    rw [he]
    have hc : P.card ≤ (t^5)^80 := by
      rw [← pow_mul, show (5 : ℕ)*80=400 by omega]
      exact hcard
    have hh := WeightedMertens.tail_three_eighths P hP (t^5) D
      (Nat.pow_pos ht) hD hlogD hc
    rw [← pow_mul, show (5 : ℕ)*30=150 by omega] at hh
    simpa only [one_div] using hh
  have hh := coveredFraction_le_general_core P S hP hSP k (t^196) (by positivity)
    hb (199/200) (by norm_num) htail
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hpow150 : (1 : ℝ) ≤ (t : ℝ)^150 := one_le_pow₀ ht1
  have hpow196 : (1 : ℝ) ≤ (t : ℝ)^196 := one_le_pow₀ ht1
  have hsmall : log (1+(t^196 : ℕ)/(199/200 : ℝ)) ≤ 3+196*log (t : ℝ) := by
    have hl := log_le_log (by positivity : (0 : ℝ) < 1+(t^196 : ℕ)/(199/200 : ℝ))
      (show 1+(t^196 : ℕ)/(199/200 : ℝ) ≤ 3*(t : ℝ)^196 by push_cast; nlinarith only [hpow196])
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'), log_pow] at hl
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hcount : (S.card : ℝ)+1 ≤ ((D : ℝ)+2)*(t : ℝ)^150 := by
    have hc : (S.card : ℝ) ≤ (D : ℝ)*(t : ℝ)^150+1 := by exact_mod_cast hScard
    nlinarith
  have hmain := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 199/200)
  have hmain' : log (199/200 : ℝ) ≤ -1/200 := by norm_num at hmain ⊢; linarith
  have hover : (S.card : ℝ)*log (1+(t^196 : ℕ)/(199/200 : ℝ))+1+log (t^196 : ℕ)/2 ≤
      (t : ℝ)^196/400 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg S.card)
    have h2 := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 3+196*log (t : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcost (show 0 ≤ (t : ℝ)^150 by positivity)
    rw [Nat.cast_pow, log_pow] 
    norm_num only [Nat.cast_ofNat]
    have he : ((t : ℝ)^46/400)*(t : ℝ)^150 = (t : ℝ)^196/400 := by ring
    push_cast at h1
    rw [he] at h3
    nlinarith only [h1,h2,h3,hlog]
  have hneg := mul_le_mul_of_nonneg_left hmain' (show 0 ≤ (t : ℝ)^196 by positivity)
  apply hh.trans
  apply exp_le_exp.mpr
  push_cast at hover ⊢
  linarith only [hover,hneg]



theorem eventually_near_critical_void_of_constants (D : ℕ)
    (hD : 1024 ≤ D)
    (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ)) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^(49/100 : ℝ)/400)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_power_exposure_budget 196 400 (by omega) (by norm_num))
  let T := max (max (78800*(D+2)) N) 1
  filter_upwards [eventually_ge_atTop (T^400)] with k hk
  intro P hP hPk
  have hT : 0 < T := by dsimp [T]; omega
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k 400 hkpos (by omega)
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by omega : 400 ≠ 0)).mp (hk.trans hkt)
  have hDt : 78800*(D+2) ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hTt)
  have hNt : N ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans hTt)
  have hh := near_critical_core_envelope P hP k t D ht (hPk.trans hkt) hD hlogD
    (near_critical_core_cost D t ht hDt) (hN t hNt k hroot)
  have hp : (k : ℝ)^(49/100 : ℝ) ≤ (t : ℝ)^196 := by
    have he := rpow_le_rpow (Nat.cast_nonneg k)
      (show (k : ℝ) ≤ (t : ℝ)^400 by exact_mod_cast hkt)
      (by norm_num : (0 : ℝ) ≤ 49/100)
    rw [← rpow_natCast (t : ℝ) 400, ← rpow_mul (Nat.cast_nonneg t)] at he
    norm_num at he ⊢
    exact he
  exact hh.trans (exp_le_exp.mpr (by linarith only [hp]))

/-- Linear-length stretched-exponential decay, uniform in every prime set. -/
theorem eventually_near_critical_linear_void :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^(49/100 : ℝ)/400)) :=
  eventually_near_critical_void_of_constants FiniteSelberg.thirteenSixteenthCutoffScale
    ((by norm_num : 1024 ≤ 65536).trans FiniteSelberg.thirteenSixteenthCutoffScale_ge)
    exposureCutoffScale_log

/-- Every fixed positive integral length power inherits the corresponding
scaled stretched exponent. This uses a larger cardinality budget, not an
independence or doubling assertion. -/
theorem eventually_power_length_void (r : ℕ) (hr : 0 < r) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P (k^r) ≤ exp (-((k : ℝ)^((r : ℝ)*(49/100))/400)) := by
  have hs := (tendsto_pow_atTop hr.ne').eventually eventually_near_critical_linear_void
  filter_upwards [hs] with k hk
  intro P hP hPk
  have hh := hk P hP (hPk.trans (Nat.le_self_pow hr.ne' k))
  simpa only [Nat.cast_pow, ← rpow_natCast (k : ℝ) r,
    ← rpow_mul (Nat.cast_nonneg k)] using hh

/-- The improved exponent at the actual quadratic length is49/50<1. -/
theorem eventually_near_critical_quadratic_void :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P (k^2) ≤ exp (-((k : ℝ)^(49/50 : ℝ)/400)) := by
  simpa only [Nat.cast_ofNat, show (2 : ℝ)*(49/100)=49/50 by norm_num]
    using eventually_power_length_void 2 (by omega)

/-- A limitation of this estimate, not a lower bound on the true void
probability: every fixed multiple of the sublinear power remains below the
k*log(k+2) entropy scale. Enlarging a fixed quadratic length constant cannot
by itself make this particular stretched-exponential envelope exclude an atom. -/
lemma eventually_subcritical_envelope_above_entropy (A : ℝ) (hA : 0 < A) :
    ∀ᶠ k : ℕ in atTop,
      exp (-((k : ℝ)*log ((k : ℝ)+2))) < exp (-A*(k : ℝ)^(49/50 : ℝ)) := by
  have hs := tendsto_natCast_atTop_atTop.eventually
    (tendsto_log_atTop.eventually (eventually_gt_atTop (A+1)))
  filter_upwards [hs,eventually_ge_atTop 1] with k hs hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (k : ℝ)^(49/50 : ℝ) ≤ k := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hk1
      (by norm_num : (49/50 : ℝ) ≤ 1)
  have hl : A < log ((k : ℝ)+2) := by
    have hh := log_le_log hk0 (show (k : ℝ) ≤ (k : ℝ)+2 by linarith)
    linarith
  have ha := mul_le_mul_of_nonneg_left hp hA.le
  have hb := mul_lt_mul_of_pos_right hl hk0
  apply exp_lt_exp.mpr
  nlinarith only [ha,hb]

#print axioms eventually_near_critical_linear_void
#print axioms eventually_near_critical_quadratic_void
#print axioms eventually_subcritical_envelope_above_entropy
end Erdos970.GapAverages
