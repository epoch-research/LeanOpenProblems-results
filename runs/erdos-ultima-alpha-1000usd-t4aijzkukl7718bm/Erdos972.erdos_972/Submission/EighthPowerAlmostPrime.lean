import Submission.FlexibleLowerSieve
import Submission.SuccessorRootAlmostPrime
import Submission.ExactLargeDivisorFirstMoment

/-! A larger roughness radius using an eighth-power Selberg cutoff and
a reduced positive margin. Prime output is not asserted. -/
namespace Erdos972EighthPowerAlmostPrime

open Finset Filter
open scoped Topology
open Erdos972FlexibleLowerSieve Erdos972RootScaleArc Erdos972PolynomialRowScales
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972PrimeAlmostPrime
open Erdos972PrimeLeastFactorScales Erdos972ExactLargeDivisorFirstMoment
open Erdos972SelbergMajorantSize Erdos972SelbergWeights
open Erdos972SelbergLowerMain Erdos972SelbergLowerTest
open Erdos972GrowingCoprimeCandidates Erdos972EfficientPrimeAlmostPrime
open Erdos972SuccessorRootAlmostPrime

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 12289

def wideRoot (u : ℕ) : ℕ := root32 (root64 u)

lemma le_wideRoot_iff (Z u : ℕ) : Z ≤ wideRoot u ↔ Z^2048 ≤ u := by
  simp only [wideRoot, le_root32_iff, le_root64_iff, ← pow_mul, Nat.reduceMul]

lemma wideRoot_tendsto : Tendsto wideRoot atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (B^2048)] with u hu
  exact (le_wideRoot_iff B u).mpr hu

lemma wideRoot_power_level (u : ℕ) : (wideRoot u)^32 ≤ root64 u :=
  (le_root32_iff (wideRoot u) (root64 u)).mp le_rfl

attribute [local irreducible] wideRoot root64

lemma wideRoot_eligible {u : ℕ} (hu : 0 < u) :
    1 ≤ wideRoot u ∧ ((wideRoot u)^8)^3*wideRoot u ≤ root64 u := by
  have hZ : 1 ≤ wideRoot u := (le_wideRoot_iff 1 u).mpr (by simpa using hu)
  refine ⟨hZ, ?_⟩
  calc
    _ = (wideRoot u)^25 := by rw [← pow_mul, ← pow_succ]
    _ ≤ (wideRoot u)^32 := Nat.pow_le_pow_right hZ (by decide)
    _ ≤ _ := wideRoot_power_level u

lemma wideRoot_successor_upper (u : ℕ) : u < (wideRoot u+1)^2048 := by
  apply Nat.lt_of_not_ge
  intro h
  have hh := (le_wideRoot_iff (wideRoot u+1) u).mpr h
  omega

lemma floor_output_successor_bound {α : ℝ} {n u : ℕ}
    (hα : α ≤ wideRoot u) (hn : n ≤ u^6) :
    floorMul α n < (wideRoot u+1)^12289 := by
  have hfloor : floorMul α n ≤ wideRoot u*n := by
    unfold floorMul
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) n))
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using hh
  have hscale : u^6 ≤ (wideRoot u+1)^12288 := by
    have hh := Nat.pow_le_pow_left (wideRoot_successor_upper u).le 6
    simpa only [← pow_mul, Nat.reduceMul] using hh
  calc
    _ ≤ wideRoot u*n := hfloor
    _ ≤ wideRoot u*(wideRoot u+1)^12288 := Nat.mul_le_mul_left _ (hn.trans hscale)
    _ < (wideRoot u+1)*(wideRoot u+1)^12288 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.pow_pos (Nat.succ_pos _))
    _ = (wideRoot u+1)^12289 := (pow_succ' _ 12288).symm

lemma rough_output_factor_bound {α : ℝ} (hα : 1 ≤ α) {n u : ℕ}
    (hn : 0 < n) (hnN : n ≤ u^6) (hαZ : α ≤ wideRoot u)
    (hc : (floorMul α n).Coprime (wideRoot u).factorial) :
    (floorMul α n).primeFactorsList.length ≤ 12288 :=
  factor_length_of_successor_bound (floorMul_pos hα hn) hc
    (floor_output_successor_bound hαZ hnN)

noncomputable def eighthConstant : ℝ := 192*majorantCap 12288

lemma eighthConstant_pos : 0 < eighthConstant :=
  mul_pos (by norm_num) (majorantCap_pos _)

/-- The stronger error budget, both sieve parameters, and all prefixes
are obtained at ONE selected irrational scale. -/
theorem exists_prime_rough_log_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < wideRoot u ∧
      (u:ℝ)^6/(eighthConstant*(1+Real.log (u+1:ℕ))) ≤
        coprimePrimeWeight α (wideRoot u).factorial (u^6) := by
  have hm := wideRoot_tendsto.eventually eventually_lowerMain_eight
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and (hm.and
      (wideRoot_tendsto.eventually_gt_atTop (max B (max 1 ⌈α⌉₊)))))
  obtain ⟨u, hBu, hu, hbudget0, hrows⟩ := exists_small_prime_prefix_rows hα hI
    (by norm_num : (0:ℝ) < 1/64) (max B T)
  have hTu : T ≤ u := (le_max_right B T).trans hBu.le
  obtain ⟨⟨hψ, _⟩, hmain, hZbig⟩ := hT u hTu
  obtain ⟨hZ, helig⟩ := wideRoot_eligible hu
  have hαZ : α ≤ wideRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 1 _).trans ((le_max_right B _).trans hZbig.le)))
  let R := (wideRoot u)^8
  have hR : 1 ≤ R := one_le_pow₀ hZ
  have hmod : R^2*wideRoot u ≤ root64 u :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hR (by decide : 2 ≤ 3))).trans helig
  have hv0 : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
  have hbudget : primeRowError u ≤ (u^6:ℕ)/(8*16*(root64 u:ℝ)) := by
    apply (le_div_iff₀ (show (0:ℝ) < 8*16*(root64 u:ℝ) by positivity)).mpr
    rw [Nat.cast_pow]
    nlinarith only [hbudget0]
  have hcap : ∀ n ∈ Ioc 0 (u^6), (floorMul α n).Coprime (wideRoot u).factorial →
      Erdos972PairSieve.majorant R (floorMul α n) ≤ majorantCap 12288 := by
    intro n hn hc
    apply majorant_bounded_factors hR (floorMul_pos hα.le (mem_Ioc.mp hn).1).ne'
    exact rough_output_factor_bound hα.le (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2 hαZ hc
  have hlower := rough_weight_log_lower_margin (Ioc 0 (u^6)) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) hR hZ helig (primeRowError_nonneg u)
    (majorantCap_pos 12288) (by norm_num : (0:ℝ) < 16) hψ hmain hbudget hcap
    (fun d hd hdR => hrows d hd (hdR.trans hmod) (u^6) le_rfl)
  rw [rough_prime_sum] at hlower
  have hR3 : R^3 ≤ root64 u := (Nat.le_mul_of_pos_right _ hZ).trans helig
  have hRu : R ≤ u :=
    (Nat.le_self_pow (by decide : 3 ≠ 0) R).trans (hR3.trans (root64_le_self u))
  refine ⟨u, (le_max_left B T).trans_lt hBu, (le_max_left B _).trans_lt hZbig, ?_⟩
  apply le_trans _ hlower
  rw [Nat.cast_pow]
  have hC := majorantCap_pos 12288
  have hL : 0 < 1+Real.log (R+1:ℕ) := by linarith only [Real.log_natCast_nonneg (R+1)]
  change (u:ℝ)^6/(192*majorantCap 12288*(1+Real.log (u+1:ℕ))) ≤ _
  apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 12*16*majorantCap 12288*(1+Real.log (R+1:ℕ)))
  have hh := mul_le_mul_of_nonneg_left (add_le_add_right
    (Erdos972ExponentialSum.monotone_log_natCast (Nat.add_le_add_right hRu 1)) 1)
    (show 0 ≤ 192*majorantCap 12288 by positivity)
  convert hh using 1 <;> ring

noncomputable def almostPrimeInputs (α : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧
    (floorMul α p).primeFactorsList.length ≤ 12288)

theorem exists_prime_almostPrime_card_scale {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧
      (u:ℝ)^6/(6*eighthConstant*(1+Real.log (u+1:ℕ))^2) ≤
        (almostPrimeInputs α (u^6)).card := by
  classical
  obtain ⟨u, hu, hZ, hweight⟩ := exists_prime_rough_log_scale hα hI (max B ⌈α⌉₊)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαZ : α ≤ wideRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right B _).trans hZ.le))
  have hcount := logarithmic_count_transfer eighthConstant_pos
    (show 0 < 1+Real.log (u+1:ℕ) by linarith only [Real.log_natCast_nonneg (u+1)])
    (hweight.trans (coprimePrimeWeight_card_upper α (wideRoot u) hu0))
  refine ⟨u, (le_max_left B _).trans_lt hu, hcount.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hprime, hc⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hprime,
    rough_output_factor_bound hα.le hprime.pos (mem_Ioc.mp hpI).2 hαZ hc⟩

theorem exists_prime_almostPrime_beyond {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) : ∃ p : ℕ, B < p ∧ p.Prime ∧
      (floorMul α p).primeFactorsList.length ≤ 12288 := by
  let T := max ⌈14*eighthConstant*(B:ℝ)⌉₊ ⌈α⌉₊
  obtain ⟨u, hu, hZ, hweight⟩ := exists_prime_rough_log_scale hα hI T
  have hu1 : 1 ≤ u := (Nat.zero_le T).trans_lt hu
  have hlargeU : 14*eighthConstant*(B:ℝ) < u :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr ((le_max_left _ _).trans_lt hu))
  have hweightLarge : 7*(B:ℝ) < coprimePrimeWeight α (wideRoot u).factorial (u^6) :=
    (seven_mul_lt_div eighthConstant_pos hlargeU).trans_le
      ((linear_below_log_weight eighthConstant_pos hu1).trans hweight)
  obtain ⟨p, hpB, hpN, hp, hpc⟩ := prime_beyond_of_coprime_weight hweightLarge
  have hαZ : α ≤ wideRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right _ _).trans hZ.le))
  exact ⟨p, hpB, hp, rough_output_factor_bound hα.le hp.pos hpN hαZ hpc⟩

theorem infinite_prime_almostPrime_inputs {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    {p : ℕ | p.Prime ∧ (floorMul α p).primeFactorsList.length ≤ 12288}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hpB, hp, hΩ⟩ := exists_prime_almostPrime_beyond hα hI B
  exact ⟨p, ⟨hp, hΩ⟩, hpB⟩

#print axioms exists_prime_rough_log_scale
#print axioms exists_prime_almostPrime_card_scale
#print axioms infinite_prime_almostPrime_inputs

end Erdos972EighthPowerAlmostPrime
