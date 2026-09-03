import Submission.MovingCenteredRows

/-! Uniform control of the centered Type-I terms for power-growing cutoffs.
The genuine Type-II term is not estimated here. -/
namespace Erdos972GrowingTypeI

open Finset ArithmeticFunction Filter
open scoped Topology
open Erdos972PrimePowerError Erdos972WeightedBeattyRows Erdos972BeattyRows
open Erdos972SelfCenteredLog Erdos972CommonLogCenter Erdos972RealLogCenter
open Erdos972ChebyshevRowMean Erdos972CenteredVaughan Erdos972ExponentialSum
open Erdos972Vaughan Erdos972CorrelationVaughan Erdos972MovingCenteredRows
open Erdos972PolynomialRowScales Erdos972CenteredRowScales

set_option maxHeartbeats 1000000

lemma typeI_uniform_budget {α E : ℝ} (hα : 1 < α) (hI : Irrational α) (hE0 : 0 ≤ E)
    {N v U V : ℕ} (hN : 0 < N) (hvN : v ≤ N) (hUv : U ≤ v) (hVv : V ≤ v) (hUVv : U*V ≤ v)
    (hrows : ∀ m : ℕ, 0 < m → m ≤ v → ∀ X ≤ floorMul (α*m) (N/m),
      |outputRow (α*m) (fun q => vonMangoldt q) X-(1/(α*m))*Chebyshev.psi X| ≤ E) :
    |first α (commonMean α N) U N|+|second α (commonMean α N) U V N|+
      |small α (commonMean α N) V N| ≤
        100*(v : ℝ)*(1+Real.log (α*N))^2*(E+1)+2*|commonLogCenter (α*N)|/α := by
  have hα0 : 0 < α := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy : 1 ≤ α*N := by nlinarith only [hα, hNR]
  have hlog : 0 ≤ Real.log (α*N) := Real.log_nonneg hy
  have hfirst := first_common_bound hα0 (hUv.trans hvN) (R := 3*Real.log (α*N)*E+25*(1+Real.log (α*N))^2) (by
    intro m hm
    obtain ⟨hm0, hmU⟩ := mem_Ioc.mp hm
    have hmv := hmU.trans hUv
    obtain ⟨hβ, hL, hlo, hhi⟩ := common_row_geometry hα hm0 (hmv.trans hvN)
    exact common_centered_log_row hβ (hI.mul_natCast (Nat.ne_of_gt hm0)) hL hlo hhi (hrows m hm0 hmv))
  have hsecond := second_uniform_bound (α := α) (ρ := commonMean α N)
    (R := E+2*Real.log (α*N)+7) (by positivity) U V N (by
      intro m hm
      obtain ⟨hm0, hmUV⟩ := mem_Ioc.mp hm
      have hmv := hmUV.trans hUVv
      obtain ⟨hβ, hL, hlo, hhi⟩ := common_row_geometry hα hm0 (hmv.trans hvN)
      exact common_centered_row hβ (hI.mul_natCast (Nat.ne_of_gt hm0)) hy (N/m) hlo hhi (hrows m hm0 hmv _ le_rfl))
  obtain ⟨hρ0, hρ7⟩ := psi_ratio_bounds (show 0 < α*N by positivity)
  have hsmall := small_bound hα.le hρ0 hρ7 V hN
  have hpsi : Chebyshev.psi V ≤ 7*(v : ℝ) := (psi_le_seven_mul (Nat.cast_nonneg V)).trans (by exact_mod_cast Nat.mul_le_mul_left 7 hVv)
  have hlogUV : Real.log (U*V : ℕ) ≤ Real.log (α*N) :=
    (monotone_log_natCast (hUVv.trans hvN)).trans (Real.log_le_log (Nat.cast_pos.mpr hN) (by nlinarith only [hα, hNR]))
  have hUR : (U : ℝ) ≤ v := Nat.cast_le.mpr hUv
  have hUVR : ((U*V : ℕ) : ℝ) ≤ v := Nat.cast_le.mpr hUVv
  have hfirst' : |first α (commonMean α N) U N| ≤
      (v : ℝ)*(3*Real.log (α*N)*E+25*(1+Real.log (α*N))^2)+2*|commonLogCenter (α*N)|/α := by
    apply hfirst.trans
    gcongr
  have hsecond' : |second α (commonMean α N) U V N| ≤
      (v : ℝ)*Real.log (α*N)*(E+2*Real.log (α*N)+7) := by
    apply hsecond.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul hUVR hlogUV (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
  have hsmall' : |small α (commonMean α N) V N| ≤ 7*(v : ℝ)*(Real.log (α*N)+7) :=
    hsmall.trans (mul_le_mul_of_nonneg_right hpsi (by positivity))
  have hpoly : 3*Real.log (α*N)*E+25*(1+Real.log (α*N))^2+
      Real.log (α*N)*(E+2*Real.log (α*N)+7)+7*(Real.log (α*N)+7) ≤
        100*(1+Real.log (α*N))^2*(E+1) := by
    nlinarith only [hlog, hE0, mul_nonneg hlog hE0, sq_nonneg (Real.log (α*N)),
      mul_nonneg (sq_nonneg (Real.log (α*N))) hE0]
  have hh := mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg (α := ℝ) v)
  linarith only [hfirst', hsecond', hsmall', hh]

lemma root64_le (u : ℕ) : root64 u ≤ u := by
  calc
    _ ≤ (root64 u)^64 := Nat.le_self_pow (by norm_num) _
    _ ≤ u := (le_root64_iff (root64 u) u).mp le_rfl

lemma root64_log_over_sixth_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k/(u : ℝ)^6) atTop (𝓝 0) := by
  have hh := root64_log_div_tendsto 1 (by norm_num) k
  simp only [one_mul] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hv0 : (0 : ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
  have hpow : (root64 u : ℝ)^2 ≤ (u : ℝ)^6 := by
    exact_mod_cast (Nat.pow_le_pow_left (root64_le u) 2).trans (Nat.pow_le_pow_right hu (by norm_num : 2 ≤ 6))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  apply (div_le_div_iff₀ (pow_pos hu0 6) hv0).mpr
  have hm := mul_le_mul_of_nonneg_right hpow (pow_nonneg (show 0 ≤ 1+Real.log u by positivity [Real.log_natCast_nonneg u]) k)
  nlinarith only [hm]

lemma summed_polynomialRowError_add_one_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k*
      (polynomialRowError u (root64 u)+1)/(u : ℝ)^6) atTop (𝓝 0) := by
  have hh := (summed_polynomialRowError_tendsto k).add (root64_log_over_sixth_tendsto k)
  simpa only [mul_add, mul_one, add_div, add_zero] using hh

lemma common_log_main_div_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ => (2*|commonLogCenter (α*N)|/α)/N) atTop (𝓝 0) := by
  have hh := commonLogCenter_div_tendsto.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hα)
  have ha := hh.abs.const_mul 2
  simp only [abs_zero, mul_zero] at ha
  apply ha.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hy : 0 ≤ α*N := by positivity
  simp only [Function.comp_apply]
  rw [abs_div, abs_of_nonneg hy]
  ring

/-- A single arbitrarily large scale controls all Vaughan cutoffs whose
product is at most the sixty-fourth root of the rational-approximation scale.
Both cutoffs may therefore grow as a fixed positive power of the main scale. -/
theorem exists_growing_typeI_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ root64 u ≤ N ∧
      ∀ U V : ℕ, U ≤ root64 u → V ≤ root64 u → U*V ≤ root64 u →
        |first α (commonMean α N) U N|+|second α (commonMean α N) U V N|+
          |small α (commonMean α N) V N| ≤ ε*N := by
  have hα0 : 0 < α := by linarith
  have hevent : ∀ᶠ u : ℕ in atTop,
      3600*(root64 u : ℝ)*(1+Real.log u)^2*(polynomialRowError u (root64 u)+1) ≤
        (ε/(4*α))*(u : ℝ)^6 := by
    have hh := (summed_polynomialRowError_add_one_tendsto 2).const_mul 3600
    simp only [mul_zero] at hh
    filter_upwards [(tendsto_order.mp hh).2 (ε/(4*α)) (by positivity), eventually_ge_atTop (1 : ℕ)] with u hu hu0
    have hup : (0 : ℝ) < u := Nat.cast_pos.mpr hu0
    rw [← mul_div_assoc] at hu
    simpa only [mul_assoc] using ((div_lt_iff₀ (pow_pos hup 6)).mp hu).le
  have hmain : ∀ᶠ N : ℕ in atTop, 2*|commonLogCenter (α*N)|/α ≤ (ε/2)*N := by
    filter_upwards [(tendsto_order.mp (common_log_main_div_tendsto hα0)).2 (ε/2) (by positivity),
      eventually_ge_atTop (1 : ℕ)] with N hN hNp
    exact ((div_lt_iff₀ (Nat.cast_pos.mpr hNp)).mp hN).le
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  obtain ⟨W, hW⟩ := eventually_atTop.mp hmain
  let C := max B (max T (max W (⌈α⌉₊+1)))
  obtain ⟨u, v, huC, hv, hvu, huv, rfl, hrows⟩ := exists_polynomial_beatty_arc_scale_root64 hα hI C
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le C) huC
  have hαu : α ≤ u := by
    apply (Nat.le_ceil α).trans
    have hh : ⌈α⌉₊+1 ≤ C := (le_max_right W _).trans ((le_max_right T _).trans (le_max_right B _))
    exact_mod_cast (Nat.le_succ ⌈α⌉₊).trans (hh.trans huC.le)
  let N := scaleCutoff α u
  obtain ⟨huN, hNu, hscale⟩ := scaleCutoff_bounds hα.le hu hαu
  have hN : 0 < N := hu.trans_le huN
  have hvN : root64 u ≤ N := (root64_le u).trans huN
  have hTu : T ≤ u := (le_max_left T _).trans ((le_max_right B _).trans huC.le)
  have hWN : W ≤ N := (le_max_left W _).trans ((le_max_right T _).trans ((le_max_right B _).trans (huC.le.trans huN)))
  have hy : 1 ≤ α*N := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith only [hα, hNR]
  have hNupper : α*N ≤ (u : ℝ)^6 := by
    have hh : (N : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    nlinarith only [(le_div_iff₀ hα0).mp hh]
  have hlog : 1+Real.log (α*N) ≤ 6*(1+Real.log u) := by
    have hh := Real.log_le_log (show 0 < α*N by positivity) hNupper
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  refine ⟨u, N, (le_max_left B _).trans_lt huC, rfl, hvN, ?_⟩
  intro U V hU hV hUV
  have hh := typeI_uniform_budget hα hI hE0 hN hvN hU hV hUV (by
    intro m hm hmv X hX
    rw [outputRow_mangoldt]
    exact hrows m hm hmv X (hX.trans (scaleCutoff_row_eligible hα.le u m (N/m) le_rfl)))
  have hbudget : 100*(root64 u : ℝ)*(1+Real.log (α*N))^2*(polynomialRowError u (root64 u)+1) ≤
      (ε/2)*N := by
    calc
      _ ≤ 3600*(root64 u : ℝ)*(1+Real.log u)^2*(polynomialRowError u (root64 u)+1) := by
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (by positivity [Real.log_nonneg hy]) hlog 2) (show 0 ≤ 100*(root64 u : ℝ) by positivity))
          (show 0 ≤ polynomialRowError u (root64 u)+1 by positivity)
        convert hm using 1 <;> ring
      _ ≤ (ε/(4*α))*(u : ℝ)^6 := hT u hTu
      _ ≤ (ε/2)*N := by
        have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ ε/(4*α) by positivity)
        have he : (ε/(4*α))*(2*α*N) = (ε/2)*N := by field_simp; ring
        rwa [he] at hm
  linarith only [hh, hbudget, hW N hWN]

#print axioms exists_growing_typeI_scale

end Erdos972GrowingTypeI
