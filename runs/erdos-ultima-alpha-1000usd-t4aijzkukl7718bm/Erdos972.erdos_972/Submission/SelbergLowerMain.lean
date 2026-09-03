import Submission.SieveMassInterval
import Submission.ChebyshevRowMean

/-! A positive main term for a lower-supported quadratic sieve test.
This still requires the actual distribution errors before it can be used
on prime inputs. -/
namespace Erdos972SelbergLowerMain

open Finset ArithmeticFunction
open Erdos972SelbergWeights Erdos972SelbergLocalCost Erdos972SieveMassInterval
open Erdos972ChebyshevRowMean Erdos972ExponentialSum Erdos972SieveMassLower

set_option maxHeartbeats 1500000

lemma reciprocal_mangoldt_bound (Z : ℕ) :
    (∑ n ∈ Ioc 0 Z, vonMangoldt n/n) ≤ 14*(1+Real.log Z) := by
  by_cases hZ : Z = 0
  · simp [hZ]
  have hZpos : 0 < Z := Nat.pos_of_ne_zero hZ
  have hZR : (0:ℝ) < Z := Nat.cast_pos.mpr hZpos
  have hpre (k : ℕ) : (∑ j ∈ range k, vonMangoldt (j+1)) = Chebyshev.psi k := by
    simp only [Chebyshev.psi, Nat.floor_natCast, sum_Ioc_zero_eq_sum_range_succ]
  have hab := sum_range_by_parts (fun j : ℕ => (1:ℝ)/(j+1 : ℕ)) (fun j => vonMangoldt (j+1)) Z
  simp only [smul_eq_mul, hpre, Nat.sub_add_cancel hZpos] at hab
  have hterm (j : ℕ) :
      -(((1:ℝ)/(j+2 : ℕ)-1/(j+1 : ℕ))*Chebyshev.psi (j+1 : ℕ)) ≤ 7/(j+2 : ℕ) := by
    have hψ := psi_le_seven_mul (Nat.cast_nonneg (α := ℝ) (j+1))
    have hj1 : (0:ℝ) < (j+1 : ℕ) := by positivity
    have hj2 : (0:ℝ) < (j+2 : ℕ) := by positivity
    have hdiff : 0 ≤ (1:ℝ)/(j+1 : ℕ)-1/(j+2 : ℕ) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hj1 (by push_cast; linarith))
    have hh := mul_le_mul_of_nonneg_left hψ hdiff
    have he : ((1:ℝ)/(j+1 : ℕ)-1/(j+2 : ℕ))*(7*(j+1 : ℕ)) = 7/(j+2 : ℕ) := by
      field_simp
      push_cast
      ring
    rw [he] at hh
    linarith only [hh]
  have hmain : (1/(Z:ℝ))*Chebyshev.psi Z ≤ 7 := by
    have hh := (div_le_iff₀ hZR).mpr (psi_le_seven_mul hZR.le)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  have hs : (∑ j ∈ range (Z-1), (1:ℝ)/(j+2 : ℕ)) ≤ (harmonic Z : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range (Z-1), (1:ℝ)/(j+1 : ℕ) := by
        apply sum_le_sum
        intro j hj
        exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
      _ ≤ ∑ j ∈ range Z, (1:ℝ)/(j+1 : ℕ) :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le Z 1)) (fun _ _ _ => by positivity)
      _ = _ := by
        rw [← sum_Ioc_zero_eq_sum_range_succ (fun n : ℕ => (1:ℝ)/n) Z]
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
        rfl
  have he : (∑ n ∈ Ioc 0 Z, vonMangoldt n/n) =
      (1/(Z:ℝ))*Chebyshev.psi Z+∑ j ∈ range (Z-1),
        -(((1:ℝ)/(j+2 : ℕ)-1/(j+1 : ℕ))*Chebyshev.psi (j+1 : ℕ)) := by
    rw [sum_Ioc_zero_eq_sum_range_succ]
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul, sum_neg_distrib, sub_eq_add_neg,
      Nat.add_assoc, Nat.reduceAdd] using hab
  rw [he]
  have hh := sum_le_sum (fun j (_ : j ∈ range (Z-1)) => hterm j)
  have hh' : (∑ j ∈ range (Z-1), (7:ℝ)/(j+2 : ℕ)) ≤ 7*(harmonic Z : ℝ) := by
    simpa only [mul_sum, mul_one_div] using mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 7)
  have hlog : 0 ≤ Real.log Z := Real.log_natCast_nonneg Z
  linarith only [hmain, hh, hh', harmonic_le_one_add_log Z, hlog]

noncomputable def smallPrimes (Z : ℕ) : Finset ℕ := (Ioc 0 Z).filter Nat.Prime

lemma reciprocal_prime_cost_bound (Z : ℕ) :
    (∑ p ∈ smallPrimes Z, (1+Real.log p)/p) ≤ 42*(1+Real.log Z) := by
  have hterm {p : ℕ} (hp : p.Prime) : (1+Real.log p)/p ≤ 3*vonMangoldt p/p := by
    rw [vonMangoldt_apply_prime hp]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hlog : (1/2:ℝ) ≤ Real.log p := by
      have h₂ : (1/2:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
      exact h₂.trans (Real.log_le_log (by norm_num) (Nat.cast_le.mpr hp.two_le))
    linarith only [hlog]
  calc
    _ ≤ ∑ p ∈ smallPrimes Z, 3*vonMangoldt p/p := sum_le_sum (fun p hp => hterm (mem_filter.mp hp).2)
    _ ≤ ∑ p ∈ Ioc 0 Z, 3*vonMangoldt p/p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => div_nonneg (mul_nonneg (by norm_num) (vonMangoldt_nonneg (n := p))) (Nat.cast_nonneg _))
    _ = 3*(∑ p ∈ Ioc 0 Z, vonMangoldt p/p) := by simp only [mul_div_assoc, mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (reciprocal_mangoldt_bound Z) (by norm_num : (0:ℝ) ≤ 3)
      nlinarith only [hh]

noncomputable def lowerMain (R Z : ℕ) : ℝ := 1/sieveMass R-∑ p ∈ smallPrimes Z, localMain R p

lemma localMain_sum_bound {R : ℕ} (hR : 1 ≤ R) (Z : ℕ) :
    (∑ p ∈ smallPrimes Z, localMain R p) ≤ 126*(1+Real.log Z)/(sieveMass R)^2 := by
  calc
    _ ≤ ∑ p ∈ smallPrimes Z, 3*(1+Real.log p)/((p:ℝ)*(sieveMass R)^2) :=
      sum_le_sum (fun p hp => localMain_upper hR (mem_filter.mp hp).2)
    _ = 3*(∑ p ∈ smallPrimes Z, (1+Real.log p)/p)/(sieveMass R)^2 := by
      simp only [sum_div, mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul_of_nonneg_left (reciprocal_prime_cost_bound Z) (by norm_num : (0:ℝ) ≤ 3)
      nlinarith only [hh]

/-- Positivity follows once the normalizing mass dominates the accumulated
small-prime costs. -/
theorem lowerMain_positive_bound {R Z : ℕ} (hR : 1 ≤ R)
    (hlarge : 252*(1+Real.log Z) ≤ sieveMass R) :
    1/(2*sieveMass R) ≤ lowerMain R Z := by
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hcost := localMain_sum_bound hR Z
  have hh : 126*(1+Real.log Z)/(sieveMass R)^2 ≤ 1/(2*sieveMass R) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hG) (by positivity)).mpr
    have ht := mul_le_mul_of_nonneg_right hlarge hG.le
    nlinarith only [ht]
  unfold lowerMain
  have he : 1/sieveMass R = 2*(1/(2*sieveMass R)) := by ring
  linarith only [hcost, hh, he]

/-- An explicit, non-optimal fixed power suffices for a positive sieve main
term. The exponent is not a primality threshold. -/
theorem lowerMain_power_positive {Z : ℕ} (hZ : 1 ≤ Z) (hlog : 1 ≤ Real.log Z) :
    1/(2*sieveMass (Z^1024)) ≤ lowerMain (Z^1024) Z := by
  apply lowerMain_positive_bound (one_le_pow₀ hZ)
  have hh := log_le_two_sieveMass (Z^1024)
  have hZ0 : 0 < (Z:ℝ) := by exact_mod_cast hZ
  have hlo : 1024*Real.log Z ≤ Real.log ((Z^1024 : ℕ)+1) := by
    have he : 1024*Real.log Z = Real.log (Z^1024 : ℕ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
    rw [he]
    exact Real.log_le_log (by positivity) (by push_cast; linarith)
  nlinarith only [hlo, hh, hlog]

#print axioms lowerMain_positive_bound
#print axioms lowerMain_power_positive

end Erdos972SelbergLowerMain
