import Submission.EighthPowerAlmostPrime
import Submission.SharpSieveMassLower

/-! A larger roughness radius using an fourth-power Selberg cutoff and
a reduced positive margin. Prime output is not asserted. -/
namespace Erdos972FourthPowerAlmostPrime

open Finset Filter
open scoped Topology
open Erdos972FlexibleLowerSieve Erdos972RootScaleArc Erdos972PolynomialRowScales
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972PrimeAlmostPrime
open Erdos972PrimeLeastFactorScales Erdos972ExactLargeDivisorFirstMoment
open Erdos972SelbergMajorantSize Erdos972SelbergWeights
open Erdos972SelbergLowerMain Erdos972SelbergLowerTest
open Erdos972GrowingCoprimeCandidates Erdos972EfficientPrimeAlmostPrime
open Erdos972SuccessorRootAlmostPrime
open Erdos972SharpSieveMassLower Erdos972SharpReciprocalPrimeCost

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 6145

/-- The sharper normalizing mass permits a fourth-power cutoff. -/
theorem eventually_lowerMain_four :
    ∀ᶠ Z : ℕ in atTop, 1/(16*sieveMass (Z^4)) ≤ lowerMain (Z^4) Z := by
  filter_upwards [eventually_primeCost_upper, eventually_ge_atTop (1:ℕ)] with Z hcost hZ
  have hR : 1 ≤ Z^4 := one_le_pow₀ hZ
  have hG : 0 < sieveMass (Z^4) := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hmass := log_le_sieveMass (Z^4)
  have hlog : 4*Real.log Z ≤ Real.log ((Z^4:ℕ)+1) := by
    have hZ0 : (0:ℝ) < Z := Nat.cast_pos.mpr hZ
    calc
      _ = Real.log (Z^4:ℕ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
      _ ≤ _ := Real.log_le_log (by positivity) (by linarith)
  have hlarge : 48*primeCost Z ≤ 15*sieveMass (Z^4) := by
    nlinarith only [hmass, hlog, hcost]
  have hsum := localMain_sum_cost hR Z
  have hcost' : 3*primeCost Z/(sieveMass (Z^4))^2 ≤ 15/(16*sieveMass (Z^4)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hG) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hlarge hG.le
    nlinarith only [hh]
  unfold lowerMain
  have he : 1/sieveMass (Z^4) = 15/(16*sieveMass (Z^4)) + 1/(16*sieveMass (Z^4)) := by ring
  linarith only [hsum, hcost', he]


def quarterRoot (u : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (root64 u))))

lemma le_quarterRoot_iff (Z u : ℕ) : Z ≤ quarterRoot u ↔ Z^1024 ≤ u := by
  rw [quarterRoot, Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt', le_root64_iff]
  norm_num only [← pow_mul]

lemma quarterRoot_tendsto : Tendsto quarterRoot atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (B^1024)] with u hu
  exact (le_quarterRoot_iff B u).mpr hu

lemma quarterRoot_power_level (u : ℕ) : (quarterRoot u)^16 ≤ root64 u := by
  apply (le_root64_iff _ _).mpr
  have hh := (le_quarterRoot_iff (quarterRoot u) u).mp le_rfl
  simpa only [← pow_mul, Nat.reduceMul] using hh

attribute [local irreducible] quarterRoot root64

lemma quarterRoot_eligible {u : ℕ} (hu : 0 < u) :
    1 ≤ quarterRoot u ∧ ((quarterRoot u)^4)^3*quarterRoot u ≤ root64 u := by
  have hZ : 1 ≤ quarterRoot u := (le_quarterRoot_iff 1 u).mpr (by simpa using hu)
  refine ⟨hZ, ?_⟩
  calc
    _ = (quarterRoot u)^13 := by rw [← pow_mul, ← pow_succ]
    _ ≤ (quarterRoot u)^16 := Nat.pow_le_pow_right hZ (by decide)
    _ ≤ _ := quarterRoot_power_level u

lemma quarterRoot_successor_upper (u : ℕ) : u < (quarterRoot u+1)^1024 := by
  apply Nat.lt_of_not_ge
  intro h
  have hh := (le_quarterRoot_iff (quarterRoot u+1) u).mpr h
  omega

lemma floor_output_successor_bound {α : ℝ} {n u : ℕ}
    (hα : α ≤ quarterRoot u) (hn : n ≤ u^6) :
    floorMul α n < (quarterRoot u+1)^6145 := by
  have hfloor : floorMul α n ≤ quarterRoot u*n := by
    unfold floorMul
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) n))
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using hh
  have hscale : u^6 ≤ (quarterRoot u+1)^6144 := by
    have hh := Nat.pow_le_pow_left (quarterRoot_successor_upper u).le 6
    simpa only [← pow_mul, Nat.reduceMul] using hh
  calc
    _ ≤ quarterRoot u*n := hfloor
    _ ≤ quarterRoot u*(quarterRoot u+1)^6144 := Nat.mul_le_mul_left _ (hn.trans hscale)
    _ < (quarterRoot u+1)*(quarterRoot u+1)^6144 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.pow_pos (Nat.succ_pos _))
    _ = (quarterRoot u+1)^6145 := (pow_succ' _ 6144).symm

lemma rough_output_factor_bound {α : ℝ} (hα : 1 ≤ α) {n u : ℕ}
    (hn : 0 < n) (hnN : n ≤ u^6) (hαZ : α ≤ quarterRoot u)
    (hc : (floorMul α n).Coprime (quarterRoot u).factorial) :
    (floorMul α n).primeFactorsList.length ≤ 6144 :=
  factor_length_of_successor_bound (floorMul_pos hα hn) hc
    (floor_output_successor_bound hαZ hnN)

noncomputable def fourthConstant : ℝ := 192*majorantCap 6144

lemma fourthConstant_pos : 0 < fourthConstant :=
  mul_pos (by norm_num) (majorantCap_pos _)

/-- The stronger error budget, both sieve parameters, and all prefixes
are obtained at ONE selected irrational scale. -/
theorem exists_prime_rough_log_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < quarterRoot u ∧
      (u:ℝ)^6/(fourthConstant*(1+Real.log (u+1:ℕ))) ≤
        coprimePrimeWeight α (quarterRoot u).factorial (u^6) := by
  have hm := quarterRoot_tendsto.eventually eventually_lowerMain_four
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and (hm.and
      (quarterRoot_tendsto.eventually_gt_atTop (max B (max 1 ⌈α⌉₊)))))
  obtain ⟨u, hBu, hu, hbudget0, hrows⟩ := exists_small_prime_prefix_rows hα hI
    (by norm_num : (0:ℝ) < 1/64) (max B T)
  have hTu : T ≤ u := (le_max_right B T).trans hBu.le
  obtain ⟨⟨hψ, _⟩, hmain, hZbig⟩ := hT u hTu
  obtain ⟨hZ, helig⟩ := quarterRoot_eligible hu
  have hαZ : α ≤ quarterRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right 1 _).trans ((le_max_right B _).trans hZbig.le)))
  let R := (quarterRoot u)^4
  have hR : 1 ≤ R := one_le_pow₀ hZ
  have hmod : R^2*quarterRoot u ≤ root64 u :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hR (by decide : 2 ≤ 3))).trans helig
  have hv0 : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
  have hbudget : primeRowError u ≤ (u^6:ℕ)/(8*16*(root64 u:ℝ)) := by
    apply (le_div_iff₀ (show (0:ℝ) < 8*16*(root64 u:ℝ) by positivity)).mpr
    rw [Nat.cast_pow]
    nlinarith only [hbudget0]
  have hcap : ∀ n ∈ Ioc 0 (u^6), (floorMul α n).Coprime (quarterRoot u).factorial →
      Erdos972PairSieve.majorant R (floorMul α n) ≤ majorantCap 6144 := by
    intro n hn hc
    apply majorant_bounded_factors hR (floorMul_pos hα.le (mem_Ioc.mp hn).1).ne'
    exact rough_output_factor_bound hα.le (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2 hαZ hc
  have hlower := rough_weight_log_lower_margin (Ioc 0 (u^6)) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) hR hZ helig (primeRowError_nonneg u)
    (majorantCap_pos 6144) (by norm_num : (0:ℝ) < 16) hψ hmain hbudget hcap
    (fun d hd hdR => hrows d hd (hdR.trans hmod) (u^6) le_rfl)
  rw [rough_prime_sum] at hlower
  have hR3 : R^3 ≤ root64 u := (Nat.le_mul_of_pos_right _ hZ).trans helig
  have hRu : R ≤ u :=
    (Nat.le_self_pow (by decide : 3 ≠ 0) R).trans (hR3.trans (root64_le_self u))
  refine ⟨u, (le_max_left B T).trans_lt hBu, (le_max_left B _).trans_lt hZbig, ?_⟩
  apply le_trans _ hlower
  rw [Nat.cast_pow]
  have hC := majorantCap_pos 6144
  have hL : 0 < 1+Real.log (R+1:ℕ) := by linarith only [Real.log_natCast_nonneg (R+1)]
  change (u:ℝ)^6/(192*majorantCap 6144*(1+Real.log (u+1:ℕ))) ≤ _
  apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 12*16*majorantCap 6144*(1+Real.log (R+1:ℕ)))
  have hh := mul_le_mul_of_nonneg_left (add_le_add_right
    (Erdos972ExponentialSum.monotone_log_natCast (Nat.add_le_add_right hRu 1)) 1)
    (show 0 ≤ 192*majorantCap 6144 by positivity)
  convert hh using 1; ring

noncomputable def almostPrimeInputs (α : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧
    (floorMul α p).primeFactorsList.length ≤ 6144)

theorem exists_prime_almostPrime_card_scale {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧
      (u:ℝ)^6/(6*fourthConstant*(1+Real.log (u+1:ℕ))^2) ≤
        (almostPrimeInputs α (u^6)).card := by
  classical
  obtain ⟨u, hu, hZ, hweight⟩ := exists_prime_rough_log_scale hα hI (max B ⌈α⌉₊)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαZ : α ≤ quarterRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right B _).trans hZ.le))
  have hcount := logarithmic_count_transfer fourthConstant_pos
    (show 0 < 1+Real.log (u+1:ℕ) by linarith only [Real.log_natCast_nonneg (u+1)])
    (hweight.trans (coprimePrimeWeight_card_upper α (quarterRoot u) hu0))
  refine ⟨u, (le_max_left B _).trans_lt hu, hcount.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hprime, hc⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hprime,
    rough_output_factor_bound hα.le hprime.pos (mem_Ioc.mp hpI).2 hαZ hc⟩

theorem exists_prime_almostPrime_beyond {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) : ∃ p : ℕ, B < p ∧ p.Prime ∧
      (floorMul α p).primeFactorsList.length ≤ 6144 := by
  let T := max ⌈14*fourthConstant*(B:ℝ)⌉₊ ⌈α⌉₊
  obtain ⟨u, hu, hZ, hweight⟩ := exists_prime_rough_log_scale hα hI T
  have hu1 : 1 ≤ u := (Nat.zero_le T).trans_lt hu
  have hlargeU : 14*fourthConstant*(B:ℝ) < u :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr ((le_max_left _ _).trans_lt hu))
  have hweightLarge : 7*(B:ℝ) < coprimePrimeWeight α (quarterRoot u).factorial (u^6) :=
    (seven_mul_lt_div fourthConstant_pos hlargeU).trans_le
      ((linear_below_log_weight fourthConstant_pos hu1).trans hweight)
  obtain ⟨p, hpB, hpN, hp, hpc⟩ := prime_beyond_of_coprime_weight hweightLarge
  have hαZ : α ≤ quarterRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right _ _).trans hZ.le))
  exact ⟨p, hpB, hp, rough_output_factor_bound hα.le hp.pos hpN hαZ hpc⟩

theorem infinite_prime_almostPrime_inputs {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    {p : ℕ | p.Prime ∧ (floorMul α p).primeFactorsList.length ≤ 6144}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hpB, hp, hΩ⟩ := exists_prime_almostPrime_beyond hα hI B
  exact ⟨p, ⟨hp, hΩ⟩, hpB⟩

#print axioms eventually_lowerMain_four
#print axioms exists_prime_rough_log_scale
#print axioms exists_prime_almostPrime_card_scale
#print axioms infinite_prime_almostPrime_inputs

end Erdos972FourthPowerAlmostPrime
