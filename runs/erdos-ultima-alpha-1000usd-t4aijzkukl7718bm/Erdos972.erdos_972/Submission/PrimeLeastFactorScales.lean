import Submission.LeastFactorCutoff
import Submission.LeastFactorSmoothMangoldt

/-! An upper bound for the least-prime-factor logarithm on genuine prime
inputs at the available irrational good scales. It improves a smoothing
comparison, but supplies no prime-pair lower bound. -/
namespace Erdos972PrimeLeastFactorScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972LeastFactorSieve Erdos972LeastFactorCutoff Erdos972LeastFactorSmoothMangoldt
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError Erdos972ChebyshevRowMean
open Erdos972SelbergLowerTest Erdos972PolynomialRowScales Erdos972PrimeRotation
open Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972SmoothMangoldt

set_option maxHeartbeats 5000000
set_option exponentiation.threshold 8192

noncomputable def primeLeastFactorMoment (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeWeight n * Real.log (floorMul α n).minFac

noncomputable def primeRowError (u : ℕ) : ℝ :=
  scaledRowError 1 u (root64 u) +
    (Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ))

lemma primeRowError_nonneg (u : ℕ) : 0 ≤ primeRowError u :=
  add_nonneg (scaledRowError_nonneg _ _ _) (sub_nonneg.mpr (Chebyshev.theta_le_psi _))

/-- A finite estimate with all the required row and cutoff conditions exposed. -/
theorem prime_least_factor_bound {α : ℝ} (hα : 1 ≤ α) {u : ℕ} (hu : 0 < u)
    (hW : 2 ≤ Nat.sqrt (Nat.sqrt (root64 u)))
    (hαZ : α ≤ layerCutoff u)
    (hbudget : primeRowError u ≤ (u^6 : ℕ)/(16*(root64 u:ℝ)))
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u →
      |row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6 : ℕ)/d| ≤
        primeRowError u) :
    primeLeastFactorMoment α (u^6) ≤ 100000*(u:ℝ)^6*(layerCount u+1) := by
  let Z := layerCutoff u
  let N := u^6
  let X := Chebyshev.psi (N : ℕ)
  let E := primeRowError u
  let L := Real.log (floorMul α N)
  have hZ2 : 2 ≤ Z := logLevel_two_le _
  have hZ1 : 1 ≤ Z := by omega
  have hZpow : Z^4 ≤ root64 u := (layerCutoff_bounds hu hW).1
  have hZmod : Z^2 ≤ root64 u :=
    (Nat.pow_le_pow_right hZ1 (by decide : 2 ≤ 4)).trans hZpow
  have hN0 : 0 < N := Nat.pow_pos hu
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hX : 0 ≤ X := Chebyshev.psi_nonneg _
  have hE : 0 ≤ E := primeRowError_nonneg u
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hXup : X ≤ 7*(N:ℝ) := psi_le_seven_mul hN
  have hEup : E*(logLevel (layerCount u):ℝ)^4 ≤ (N:ℝ) := by
    have hv0 : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
    have hb := (le_div_iff₀ (show 0 < 16*(root64 u:ℝ) by positivity)).mp hbudget
    have hz : (Z:ℝ)^4 ≤ root64 u := by
      simpa only [Nat.cast_pow] using (Nat.cast_le.mpr hZpow : ((Z^4:ℕ):ℝ) ≤ root64 u)
    have hh := mul_le_mul_of_nonneg_left hz hE
    have hn : 0 ≤ E*(root64 u:ℝ) := mul_nonneg hE (Nat.cast_nonneg _)
    change E*(Z:ℝ)^4 ≤ (N:ℝ)
    change E*(16*(root64 u:ℝ)) ≤ (N:ℝ) at hb
    nlinarith only [hb, hh, hn]
  have hLup : L ≤ 5000*Real.log (logLevel (layerCount u)) := by
    have hMpos : 0 < floorMul α N := floorMul_pos hα hN0
    have hb := floor_output_layer_bound hu hW hαZ (le_refl (u^6))
    have hh := Real.log_le_log (Nat.cast_pos.mpr hMpos) (Nat.cast_le.mpr hb)
    rw [Nat.cast_pow, Real.log_pow] at hh
    have hlog : 0 ≤ Real.log Z := Real.log_natCast_nonneg _
    change L ≤ 5000*Real.log Z
    norm_num only [Nat.cast_ofNat] at hh
    change L ≤ 4993*Real.log Z at hh
    linarith only [hh, hlog]
  have hy (n : ℕ) (hn : n ∈ Ioc 0 N) : Real.log (floorMul α n).minFac ≤ L := by
    have hnpos := floorMul_pos hα (mem_Ioc.mp hn).1
    have hle : (floorMul α n).minFac ≤ floorMul α N :=
      (Nat.minFac_le hnpos).trans ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2)
    exact Real.log_le_log (Nat.cast_pos.mpr (Nat.minFac_pos _)) (Nat.cast_le.mpr hle)
  have hh := weighted_least_factor_upper (Ioc 0 N) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) hX hE hL hy (layerCount u)
    (fun d hd hdZ => hrows d hd (hdZ.trans hZmod))
  apply hh.trans
  have hb := leastFactorBudget_linear (layerCount u) hN hX hE hXup hEup hLup
  simpa only [N, Nat.cast_pow] using hb

/-- The actual one-prime rows supply the preceding estimate at arbitrarily
large scales for every prescribed irrational slope. -/
theorem exists_prime_least_factor_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      primeLeastFactorMoment α (u^6) ≤ 100000*(u:ℝ)^6*(layerCount u+1) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and
      ((root64_tendsto.eventually_ge_atTop 2048).and
        (((nat_fourth_root_tendsto.comp root64_tendsto).eventually_ge_atTop 2).and
          ((layerCutoff_tendsto.eventually_ge_atTop ⌈α⌉₊).and
            (layerCount_tendsto.eventually_gt_atTop B)))))
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  clear_value u
  obtain ⟨⟨_, hbudget⟩, hv, hW, hαZ, hBJ⟩ := hT u hTu
  have hαcut : α ≤ layerCutoff u := (Nat.le_ceil α).trans (Nat.cast_le.mpr hαZ)
  refine ⟨u, hBu, hBJ, prime_least_factor_bound hα.le hu hW hαcut hbudget ?_⟩
  intro d hd hdv
  exact prime_row_discrepancy α d (u^6) (input_divisor_row_discrepancy
    (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
    (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi) hd hdv le_rfl)

noncomputable def mixedPrimeSmooth (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeWeight n*smoothMangoldt t (floorMul α n)

noncomputable def mixedPrimeMangoldt (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeWeight n*Λ (floorMul α n)

lemma mixed_error_least_factor {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (N : ℕ) :
    |mixedPrimeSmooth t α N-mixedPrimeMangoldt α N| ≤
      t*Real.log (floorMul α N)*primeLeastFactorMoment α N := by
  apply weighted_smooth_error (Ioc 0 N) primeWeight (floorMul α) ht
    (fun n _ => primeWeight_nonneg n)
  intro n hn
  exact Real.log_le_log (Nat.cast_pos.mpr (floorMul_pos hα (mem_Ioc.mp hn).1))
    (Nat.cast_le.mpr ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2))

/-- A joint parameter adapted to the least-factor moment. Its denominator
has one input logarithm and the square of the number of logarithmic layers. -/
noncomputable def layerParameter (α : ℝ) (u : ℕ) : ℝ :=
  1/((1+Real.log (floorMul α (u^6)))*(layerCount u+1)^2)

lemma layerParameter_pos (α : ℝ) (u : ℕ) : 0 < layerParameter α u := by
  unfold layerParameter
  positivity [Real.log_natCast_nonneg (floorMul α (u^6))]

/-- A finite mixed-correlation comparison at any scale satisfying the
least-factor bound. The comparison does not supply a positive main term. -/
theorem layerParameter_mixed_error {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hbound : primeLeastFactorMoment α (u^6) ≤ 100000*(u:ℝ)^6*(layerCount u+1)) :
    |mixedPrimeSmooth (layerParameter α u) α (u^6)-mixedPrimeMangoldt α (u^6)| ≤
      100000*(u:ℝ)^6/(layerCount u+1) := by
  have hh := mixed_error_least_factor hα (layerParameter_pos α u) (u^6)
  apply hh.trans
  have hlo := Real.log_natCast_nonneg (floorMul α (u^6))
  have ht := layerParameter_pos α u
  have hb := mul_le_mul_of_nonneg_left hbound (mul_nonneg ht.le hlo)
  apply hb.trans
  unfold layerParameter
  have hJ : (0:ℝ) < layerCount u+1 := by positivity
  have hL : 0 < 1+Real.log (floorMul α (u^6)) := by positivity
  apply (le_div_iff₀ hJ).mpr
  field_simp
  nlinarith only [mul_nonneg (show 0 ≤ (u:ℝ)^6 by positivity)
    (show 0 ≤ (layerCount u:ℝ)+1 by positivity)]

lemma layer_error_envelope_tendsto :
    Tendsto (fun u : ℕ => (100000:ℝ)/(layerCount u+1)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_atTop_add_const_right atTop 1
    (tendsto_natCast_atTop_atTop.comp layerCount_tendsto)

/-- The sharper mixed comparison is available with arbitrarily small
normalized error at arbitrarily large genuine irrational good scales. -/
theorem exists_layerParameter_small_error {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      |mixedPrimeSmooth (layerParameter α u) α (u^6)-mixedPrimeMangoldt α (u^6)| ≤
        ε*(u:ℝ)^6 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((tendsto_order.mp layer_error_envelope_tendsto).2 ε hε)
  obtain ⟨u, hBu, hBJ, hb⟩ := exists_prime_least_factor_scale hα hI (max B T)
  have huT : T ≤ u := (le_max_right B T).trans hBu.le
  have he := mul_le_mul_of_nonneg_right (hT u huT).le (show 0 ≤ (u:ℝ)^6 by positivity)
  refine ⟨u, (le_max_left _ _).trans_lt hBu, (le_max_left _ _).trans_lt hBJ, ?_⟩
  apply (layerParameter_mixed_error hα.le hb).trans
  convert he using 1; ring

lemma mixedPrimeMangoldt_bounds (α : ℝ) (N : ℕ) :
    primeCorrelation α N ≤ mixedPrimeMangoldt α N ∧
      mixedPrimeMangoldt α N ≤ mangoldtCorrelation α N := by
  classical
  constructor
  · unfold primeCorrelation mixedPrimeMangoldt
    rw [sum_filter]
    apply sum_le_sum
    intro n hn
    split_ifs with hp
    · rw [primeWeight, if_pos hp.1, vonMangoldt_apply_prime hp.2]
    · exact mul_nonneg (primeWeight_nonneg n) vonMangoldt_nonneg
  · unfold mixedPrimeMangoldt mangoldtCorrelation
    apply sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_right _ vonMangoldt_nonneg
    unfold primeWeight
    split_ifs with hp
    · rw [vonMangoldt_apply_prime hp]
    · exact vonMangoldt_nonneg

lemma mixedPrimeMangoldt_prime_error_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ => (mixedPrimeMangoldt α N-primeCorrelation α N)/N)
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (Erdos972CorrelationVaughan.primePowerBudget_div_tendsto hα)
  · filter_upwards with N
    exact div_nonneg (sub_nonneg.mpr (mixedPrimeMangoldt_bounds α N).1) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have he := (prime_power_error_bound_sharp hα hN).2
    change mangoldtCorrelation α N-primeCorrelation α N ≤
      Erdos972CorrelationVaughan.primePowerBudget α N at he
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) N)
    linarith only [he, (mixedPrimeMangoldt_bounds α N).2]

/-- The comparison ultimately concerns genuine prime pairs: the remaining
prime-power output error is also negligible. No positive lower bound for
the mixed smoothed sum is asserted. -/
theorem exists_layerParameter_prime_comparison {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      |mixedPrimeSmooth (layerParameter α u) α (u^6)-primeCorrelation α (u^6)| ≤
        ε*(u:ℝ)^6 := by
  have hpow : Tendsto (fun u : ℕ => u^6) atTop atTop :=
    tendsto_atTop_mono (fun u => Nat.le_pow (by decide : 0 < 6)) tendsto_id
  have hh := (mixedPrimeMangoldt_prime_error_tendsto hα.le).comp hpow
  have hevent : ∀ᶠ u : ℕ in atTop,
      |mixedPrimeMangoldt α (u^6)-primeCorrelation α (u^6)| ≤ (ε/2)*(u:ℝ)^6 := by
    filter_upwards [(tendsto_order.mp hh).2 (ε/2) (by positivity),
      eventually_ge_atTop (1:ℕ)] with u hu hu1
    have hpos : (0:ℝ) < (u^6:ℕ) := Nat.cast_pos.mpr (Nat.pow_pos hu1)
    have hd := (div_lt_iff₀ hpos).mp hu
    rw [abs_of_nonneg (sub_nonneg.mpr (mixedPrimeMangoldt_bounds α (u^6)).1)]
    simpa only [Nat.cast_pow] using hd.le
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  obtain ⟨u, hu, hj, he⟩ := exists_layerParameter_small_error hα hI
    (show 0 < ε/2 by positivity) (max B T)
  refine ⟨u, (le_max_left _ _).trans_lt hu, (le_max_left _ _).trans_lt hj, ?_⟩
  have hp := hT u ((le_max_right _ _).trans hu.le)
  exact (abs_sub_le _ (mixedPrimeMangoldt α (u^6)) _).trans (by linarith only [he, hp])

#print axioms exists_prime_least_factor_scale
#print axioms layerParameter_mixed_error
#print axioms exists_layerParameter_small_error
#print axioms exists_layerParameter_prime_comparison

end Erdos972PrimeLeastFactorScales
