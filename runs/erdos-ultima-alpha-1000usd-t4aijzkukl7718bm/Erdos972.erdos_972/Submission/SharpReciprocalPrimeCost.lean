import Submission.SelbergLowerMain
import Submission.CommonLogCenter

/-! An elementary Mertens upper bound sharply reduces the local prime cost
in the lower sieve. No quantitative prime number theorem is used. -/
namespace Erdos972SharpReciprocalPrimeCost

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta
open Erdos972SelbergLowerMain Erdos972SelbergWeights Erdos972SelbergLocalCost
open Erdos972SieveMassInterval Erdos972SieveMassLower Erdos972ChebyshevRowMean
open Erdos972CorrelationVaughan Erdos972CommonLogCenter Erdos972ExponentialSum

set_option maxHeartbeats 1500000

lemma mangoldt_floor_sum (N : ℕ) :
    (∑ d ∈ Ioc 0 N, vonMangoldt d*(N/d:ℕ)) = logMass N := by
  have hh := weightedSum_convolution vonMangoldt (ζ : ArithmeticFunction ℝ) (fun _ => 1) N
  rw [vonMangoldt_mul_zeta] at hh
  have hinner (d : ℕ) : (∑ n ∈ Ioc 0 (N/d), (ζ : ArithmeticFunction ℝ) n*1) = (N/d:ℕ) := by
    calc
      _ = ∑ n ∈ Ioc 0 (N/d), (1:ℝ) := by
        apply sum_congr rfl
        intro n hn
        simp only [natCoe_apply, zeta_apply_ne (mem_Ioc.mp hn).1.ne', Nat.cast_one, mul_one]
      _ = _ := by simp
  simp_rw [hinner] at hh
  simpa only [weightedSum, log_apply, mul_one, logMass] using hh.symm

/-- The additive constant is uniform in the endpoint. -/
theorem reciprocal_mangoldt_log_upper (N : ℕ) :
    (∑ d ∈ Ioc 0 N, vonMangoldt d/d) ≤ Real.log N+7 := by
  by_cases hN : N = 0
  · simp [hN]
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN0
  have hterm (d : ℕ) : (N:ℝ)*(vonMangoldt d/d) ≤ vonMangoldt d*(N/d:ℕ)+vonMangoldt d := by
    have hh := Nat.lt_floor_add_one ((N:ℝ)/d)
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at hh
    have hm := mul_le_mul_of_nonneg_left hh.le (vonMangoldt_nonneg (n := d))
    calc
      _ = vonMangoldt d*((N:ℝ)/d) := by ring
      _ ≤ _ := hm
      _ = _ := by ring
  have hsum := sum_le_sum (fun d (_ : d ∈ Ioc 0 N) => hterm d)
  rw [← mul_sum, sum_add_distrib, mangoldt_floor_sum] at hsum
  have hψ : (∑ d ∈ Ioc 0 N, vonMangoldt d) ≤ 7*(N:ℝ) := by
    simpa only [Chebyshev.psi, Nat.floor_natCast] using psi_le_seven_mul (Nat.cast_nonneg (α := ℝ) N)
  have hlog : logMass N ≤ (N:ℝ)*Real.log N := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, Real.log N := sum_le_sum
        (fun n hn => monotone_log_natCast (mem_Ioc.mp hn).2)
      _ = _ := by simp
  have hmul : (N:ℝ)*(∑ d ∈ Ioc 0 N, vonMangoldt d/d) ≤ (N:ℝ)*(Real.log N+7) := by
    nlinarith only [hsum, hψ, hlog]
  exact (mul_le_mul_iff_right₀ hNR).mp hmul

noncomputable def primeCost (Z : ℕ) : ℝ := ∑ p ∈ smallPrimes Z, (1+Real.log p)/p

lemma primeCost_split_upper {P : ℕ} (_hP : 0 < P) (hlogP : 8 ≤ Real.log P) (Z : ℕ) :
    primeCost Z ≤ (9/8:ℝ)*Real.log Z+(63/8:ℝ)+(harmonic P:ℝ) := by
  have hsmall : (∑ p ∈ smallPrimes Z, if p ≤ P then (1:ℝ)/p else 0) ≤ (harmonic P:ℝ) := by
    rw [← sum_filter]
    calc
      _ ≤ ∑ p ∈ Ioc 0 P, (1:ℝ)/p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpS, hpP⟩ := mem_filter.mp hp
          exact mem_Ioc.mpr ⟨(mem_filter.mp hpS).2.pos, hpP⟩
        · intro p hp hnot
          positivity
      _ = _ := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
        rfl
  have hterm {p : ℕ} (hp : p ∈ smallPrimes Z) :
      (1+Real.log p)/p ≤ (9/8:ℝ)*vonMangoldt p/p + if p ≤ P then (1:ℝ)/p else 0 := by
    have hprime := (mem_filter.mp hp).2
    have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hprime.pos
    rw [vonMangoldt_apply_prime hprime]
    by_cases hpP : p ≤ P
    · rw [if_pos hpP, ← add_div]
      apply div_le_div_of_nonneg_right _ hpR.le
      nlinarith only [Real.log_natCast_nonneg p]
    · rw [if_neg hpP, add_zero]
      have hpL : 8 ≤ Real.log p := hlogP.trans (monotone_log_natCast (Nat.le_of_lt (lt_of_not_ge hpP)))
      apply div_le_div_of_nonneg_right _ hpR.le
      nlinarith only [hpL]
  have hb : (∑ p ∈ smallPrimes Z, vonMangoldt p/p) ≤ Real.log Z+7 := by
    apply le_trans _ (reciprocal_mangoldt_log_upper Z)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p hp _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  have hs := sum_le_sum (fun p hp => hterm hp)
  rw [sum_add_distrib] at hs
  have hscale : (∑ p ∈ smallPrimes Z, (9/8:ℝ)*vonMangoldt p/p) ≤
      (9/8:ℝ)*(Real.log Z+7) := by
    simpa only [mul_sum, mul_div_assoc] using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 9/8)
  change primeCost Z ≤ _ at hs
  linarith only [hs, hscale, hsmall]

theorem eventually_primeCost_upper :
    ∀ᶠ Z : ℕ in atTop, primeCost Z ≤ (5/4:ℝ)*Real.log Z := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨P, hP0, hP8⟩ := ((eventually_ge_atTop (1:ℕ)).and (hlog.eventually_ge_atTop 8)).exists
  have hC := hlog.eventually_ge_atTop (8*((63/8:ℝ)+(harmonic P:ℝ)))
  filter_upwards [hC] with Z hZ
  change 8*((63/8:ℝ)+(harmonic P:ℝ)) ≤ Real.log Z at hZ
  have hh := primeCost_split_upper hP0 hP8 Z
  linarith only [hh, hZ]

lemma localMain_sum_cost {R : ℕ} (hR : 1 ≤ R) (Z : ℕ) :
    (∑ p ∈ smallPrimes Z, localMain R p) ≤ 3*primeCost Z/(sieveMass R)^2 := by
  calc
    _ ≤ ∑ p ∈ smallPrimes Z, 3*(1+Real.log p)/((p:ℝ)*(sieveMass R)^2) :=
      sum_le_sum (fun p hp => localMain_upper hR (mem_filter.mp hp).2)
    _ = _ := by
      simp only [primeCost, sum_div, mul_sum]
      apply sum_congr rfl
      intro p hp
      ring

/-- A fixed sixteenth power now suffices, at all sufficiently large cutoffs. -/
theorem eventually_lowerMain_sixteen :
    ∀ᶠ Z : ℕ in atTop, 1/(2*sieveMass (Z^16)) ≤ lowerMain (Z^16) Z := by
  filter_upwards [eventually_primeCost_upper, eventually_ge_atTop (1:ℕ)] with Z hcost hZ
  have hR : 1 ≤ Z^16 := one_le_pow₀ hZ
  have hG : 0 < sieveMass (Z^16) := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hmass := log_le_two_sieveMass (Z^16)
  have hlog : 16*Real.log Z ≤ Real.log ((Z^16:ℕ)+1) := by
    have hZ0 : (0:ℝ) < Z := Nat.cast_pos.mpr hZ
    calc
      _ = Real.log (Z^16:ℕ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
      _ ≤ _ := Real.log_le_log (by positivity) (by linarith)
  have hlarge : 6*primeCost Z ≤ sieveMass (Z^16) := by
    nlinarith only [hmass, hlog, hcost, Real.log_natCast_nonneg Z]
  have hsum := localMain_sum_cost hR Z
  have hhalf : 3*primeCost Z/(sieveMass (Z^16))^2 ≤ 1/(2*sieveMass (Z^16)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hG) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hlarge hG.le
    nlinarith only [hh]
  unfold lowerMain
  have he : 1/sieveMass (Z^16) = 2*(1/(2*sieveMass (Z^16))) := by ring
  linarith only [hsum, hhalf, he]

#print axioms reciprocal_mangoldt_log_upper
#print axioms eventually_primeCost_upper
#print axioms eventually_lowerMain_sixteen

end Erdos972SharpReciprocalPrimeCost
