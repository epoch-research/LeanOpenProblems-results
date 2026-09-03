import Submission.RawMobiusCutoffEnergy
import Submission.FullSmoothL1Obstruction
import Submission.CesaroLogarithmicMean

/-! The adaptive polylogarithmic-power detector does not admit a uniformly
small raw finite-divisor tail in normalized mean square. This is an
obstruction to that approximation method, not to the Erdős conjecture. -/
namespace Erdos972PolylogPowerDivisorEnergy

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972PolylogPowerDivisorLimit Erdos972PolylogPowerPrimeDetector
open Erdos972RawMobiusCutoffEnergy Erdos972SelbergWeights
open Erdos972DampedSingleMean Erdos972FullSmoothL1Obstruction
open Erdos972CesaroLogarithmicMean

set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma cesaro_Ioc {f : ℕ → ℝ} {L : ℝ} (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, f n)/(N : ℝ)) atTop (𝓝 L) := by
  have hh := (hf.comp (tendsto_add_atTop_nat 1)).cesaro
  simpa only [Function.comp_def, ← sum_Ioc_eq_sum_range_succ, div_eq_mul_inv, mul_comm] using hh

lemma raw_square_prefix (D N : ℕ) :
    (∑ n ∈ Ioc 0 N, (truncatedMobius D n)^2) =
      ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 D,
        (μ d : ℝ)*(μ e : ℝ)*(N/(d.lcm e) : ℕ) := by
  simp only [truncatedMobius, pow_two, sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have ht (n : ℕ) : (if d ∣ n then (μ d : ℝ) else 0)*(if e ∣ n then (μ e : ℝ) else 0) =
      if d.lcm e ∣ n then (μ d : ℝ)*(μ e : ℝ) else 0 := by
    by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [Nat.lcm_dvd_iff, hd, he]
  simp_rw [ht]
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

lemma raw_square_mean_tendsto (D : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (truncatedMobius D n)^2)/(N : ℝ))
      atTop (𝓝 (quadraticMain D (fun d => (μ d : ℝ)))) := by
  have hh := tendsto_finset_sum (Ioc 0 D) (fun d _ =>
    tendsto_finset_sum (Ioc 0 D) (fun e _ =>
      (nat_div_ratio_tendsto (d.lcm e)).const_mul ((μ d : ℝ)*(μ e : ℝ))))
  simpa only [raw_square_prefix, sum_div, quadraticMain, ← mul_div_assoc, mul_one] using hh

lemma raw_square_factorial_mean (D : ℕ) :
    (∑ n ∈ Ioc 0 D.factorial, (truncatedMobius D n)^2)/(D.factorial : ℝ) =
      quadraticMain D (fun d => (μ d : ℝ)) := by
  rw [raw_square_prefix, sum_div, quadraticMain]
  apply sum_congr rfl
  intro d hd
  rw [sum_div]
  apply sum_congr rfl
  intro e he
  have hl : d.lcm e ∣ D.factorial := Nat.lcm_dvd
    (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2)
    (Nat.dvd_factorial (mem_Ioc.mp he).1 (mem_Ioc.mp he).2)
  have hl0 : (d.lcm e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.lcm_ne_zero (mem_Ioc.mp hd).1.ne' (mem_Ioc.mp he).1.ne')
  have hF : (D.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos D).ne'
  rw [Nat.cast_div hl hl0]
  field_simp

lemma raw_square_mean_pos_lower {D : ℕ} (hD : 1 ≤ D) :
    1/(D.factorial : ℝ) ≤ quadraticMain D (fun d => (μ d : ℝ)) := by
  have h1 : truncatedMobius D 1 = 1 := by
    unfold truncatedMobius
    simp only [Nat.dvd_one]
    rw [sum_eq_single 1]
    · simp
    · intro d hd hne
      simp [hne]
    · intro hh
      exact (hh (mem_Ioc.mpr ⟨by decide, hD⟩)).elim
  have hh := single_le_sum (f := fun n => (truncatedMobius D n)^2)
    (fun n hn => sq_nonneg _)
    (show 1 ∈ Ioc 0 D.factorial from mem_Ioc.mpr ⟨by decide, Nat.factorial_pos D⟩)
  dsimp only at hh
  rw [h1, one_pow] at hh
  have hbound := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) D.factorial)
  rwa [raw_square_factorial_mean] at hbound

noncomputable def uniformEnergyFloor : ℝ := min (1/200) (1/((80000 : ℕ).factorial : ℝ))

lemma uniformEnergyFloor_pos : 0 < uniformEnergyFloor := by
  unfold uniformEnergyFloor
  exact lt_min (by norm_num) (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _)))

lemma uniformEnergyFloor_le {D : ℕ} (hD : 1 ≤ D) :
    uniformEnergyFloor ≤ quadraticMain D (fun d => (μ d : ℝ)) := by
  by_cases hlarge : 80000 ≤ D
  · exact (min_le_left _ _).trans (quadraticMain_mobius_lower hlarge)
  · apply (min_le_right _ _).trans
    apply (one_div_le_one_div_of_le (Nat.cast_pos.mpr (Nat.factorial_pos D))
      (Nat.cast_le.mpr (Nat.factorial_le (by omega : D ≤ 80000)))).trans
    exact raw_square_mean_pos_lower hD

lemma powerDetector_square_bound (n : ℕ) :
    (powerDetector n)^2 ≤ (if n.Prime then (1 : ℝ) else 0)+compositePowerError n := by
  have h0 := powerDetector_nonneg n
  have h1 := powerDetector_le_one n
  have hs : (powerDetector n)^2 ≤ powerDetector n := by nlinarith only [h0, h1]
  apply hs.trans
  unfold compositePowerError
  by_cases hp : n.Prime
  · simpa only [if_pos hp, add_zero] using h1
  · simp only [if_neg hp, zero_add, le_refl]

lemma powerDetector_square_mean_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (powerDetector n)^2)/(N : ℝ)) atTop (𝓝 0) := by
  have hc := cesaro_Ioc summable_compositePowerError.tendsto_atTop_zero
  have hh := primeCounting_div_tendsto_zero.add hc
  simp only [add_zero] at hh
  apply squeeze_zero (fun N => by positivity) (fun N => ?_) hh
  have hb := sum_le_sum (fun n (_ : n ∈ Ioc 0 N) => powerDetector_square_bound n)
  rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, prime_card_eq] at hb
  simpa only [add_div] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)

lemma coefficient_error_square_mean_tendsto_zero (D : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N,
      (truncatedDetector D n-truncatedMobius D n)^2)/(N : ℝ)) atTop (𝓝 0) := by
  simpa only [zero_pow (by decide : 2 ≠ 0)] using
    cesaro_Ioc ((truncatedDetector_sub_mobius_tendsto D).pow 2)

lemma three_square_bound (a b c : ℝ) :
    c^2 ≤ 3*((a-c)^2+(a-b)^2+b^2) := by
  nlinarith only [sq_nonneg ((c-a)-(a-b)), sq_nonneg ((a-b)-b), sq_nonneg (b-(c-a))]

/-- A hypothetical uniform energy bound necessarily dominates a positive
fraction of the raw Möbius quadratic mean. -/
theorem energy_bound_forces_quadratic_bound (D : ℕ) (ε : ℝ)
    (hbound : ∀ N : ℕ, (∑ n ∈ Ioc 0 N,
      (truncatedDetector D n-powerDetector n)^2) ≤ ε*N) :
    quadraticMain D (fun d => (μ d : ℝ)) ≤ 3*ε := by
  have hh := ((raw_square_mean_tendsto D).sub
    ((coefficient_error_square_mean_tendsto_zero D).const_mul 3)).sub
      (powerDetector_square_mean_tendsto_zero.const_mul 3)
  simp only [mul_zero, sub_zero] at hh
  apply le_of_tendsto hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs := sum_le_sum (fun n (_ : n ∈ Ioc 0 N) =>
    three_square_bound (truncatedDetector D n) (powerDetector n) (truncatedMobius D n))
  simp only [sum_add_distrib, ← mul_sum] at hs
  have he := hbound N
  have hd := div_le_div_of_nonneg_right hs hNR.le
  have hb := (div_le_iff₀ hNR).mpr he
  simp only [mul_add, add_div, mul_div_assoc] at hd
  linarith only [hd, hb]

/-- For all large cutoffs, a fixed numerical error tolerance already fails. -/
theorem large_cutoff_energy_failure {D : ℕ} (hD : 80000 ≤ D) :
    ∃ N : ℕ, 0 < N ∧ (1/1000 : ℝ)*N <
      ∑ n ∈ Ioc 0 N, (truncatedDetector D n-powerDetector n)^2 := by
  by_contra hnot
  have hb : ∀ N : ℕ, (∑ n ∈ Ioc 0 N,
      (truncatedDetector D n-powerDetector n)^2) ≤ (1/1000 : ℝ)*N := by
    intro N
    by_cases hN : 0 < N
    · exact le_of_not_gt (fun hh => hnot ⟨N, hN, hh⟩)
    · have hz : N = 0 := by omega
      simp [hz]
  have hq := energy_bound_forces_quadratic_bound D (1/1000) hb
  have hl := quadraticMain_mobius_lower hD
  linarith only [hq, hl]

/-- No fixed raw divisor cutoff gives arbitrarily small normalized
mean-square error for the actual adaptive polylogarithmic detector. -/
theorem no_fixed_uniform_energy_cutoff :
    ∃ ε : ℝ, 0 < ε ∧ ∀ D : ℕ, 1 ≤ D → ∃ N : ℕ, 0 < N ∧
      ε*N < ∑ n ∈ Ioc 0 N, (truncatedDetector D n-powerDetector n)^2 := by
  refine ⟨uniformEnergyFloor/4, by positivity [uniformEnergyFloor_pos], ?_⟩
  intro D hD
  by_contra hnot
  have hb : ∀ N : ℕ, (∑ n ∈ Ioc 0 N,
      (truncatedDetector D n-powerDetector n)^2) ≤ (uniformEnergyFloor/4)*N := by
    intro N
    by_cases hN : 0 < N
    · exact le_of_not_gt (fun hh => hnot ⟨N, hN, hh⟩)
    · have hz : N = 0 := by omega
      simp [hz]
  have hq := energy_bound_forces_quadratic_bound D (uniformEnergyFloor/4) hb
  have hl := uniformEnergyFloor_le hD
  linarith only [hq, hl, uniformEnergyFloor_pos]

#print axioms raw_square_mean_tendsto
#print axioms uniformEnergyFloor_le
#print axioms powerDetector_square_mean_tendsto_zero
#print axioms large_cutoff_energy_failure
#print axioms no_fixed_uniform_energy_cutoff

end Erdos972PolylogPowerDivisorEnergy
