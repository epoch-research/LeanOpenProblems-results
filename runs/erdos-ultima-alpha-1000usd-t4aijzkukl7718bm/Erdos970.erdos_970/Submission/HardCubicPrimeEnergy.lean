import Submission.HardCubicPrimeProfile

/-! The hard-cubic prime energy main term. The reciprocal-prime accumulation
of the jump error remains explicit in the quantitative lower bound. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma prime_log_moment_succ (R : ℕ) (hR : 0 < R) (n : ℕ) :
    |(∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ (n + 1) / p) -
      log (R : ℝ) ^ (n + 1) / ((n : ℝ) + 1)| ≤
      2 * sharpMomentError * log (R : ℝ) ^ n := by
  cases n with
  | zero =>
    have hh := abs_primeSum_sub_log R hR
    simp only [Nat.zero_add, pow_one, Nat.cast_zero, zero_add, div_one, pow_zero, mul_one]
    change |primeSum R - log (R : ℝ)| ≤ _
    unfold sharpMomentError
    linarith [boundConstant_pos]
  | succ n =>
    convert prime_log_moment R hR n using 1 <;> push_cast <;> ring

end Erdos970.WeightedMertens
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

lemma cappedLogMoment_succ_error (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) (n : ℕ) :
    |cappedLogMoment p (log R) (n + 1) -
      (log (R : ℝ) ^ (n + 1) / ((n : ℝ) + 1) +
        log (R : ℝ) ^ (n + 1) * ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ))| ≤
      2 * WeightedMertens.sharpMomentError * log (R : ℝ) ^ n := by
  rw [cappedLogMoment_split p hp hinj R hR hfull]
  have he (A B C : ℝ) : A + B - (C + B) = A - C := by ring
  rw [he]
  exact WeightedMertens.prime_log_moment_succ R hR n

lemma hardCubicShiftMain_prime_sum (p : ι → ℕ) (L : ℝ) :
    (∑ i, (1 / (p i : ℝ)) * hardCubicShiftMain L (min (log (p i : ℝ)) L)) =
      5721664 * L ^ 6 * cappedLogMoment p L 1 +
      (428544696 / 5) * L ^ 5 * cappedLogMoment p L 2 -
      (434463325 / 6) * L ^ 4 * cappedLogMoment p L 3 +
      49600525 * L ^ 3 * cappedLogMoment p L 4 -
      (147536616 / 5) * L ^ 2 * cappedLogMoment p L 5 +
      9217325 * L * cappedLogMoment p L 6 - (239589779 / 70) * cappedLogMoment p L 7 := by
  unfold hardCubicShiftMain cappedLogMoment
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

lemma prime_hardCubic_shift_main_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    (∑ i, (1 / (p i : ℝ)) * hardCubicShiftMain (log R) (min (log (p i : ℝ)) (log R))) ≤
      (hardCubicEnergy + hardCubicNorm *
        ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) * log (R : ℝ) ^ 7 +
      1000000000 * WeightedMertens.sharpMomentError * log (R : ℝ) ^ 6 := by
  let L := log (R : ℝ)
  let T := ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)
  let e := WeightedMertens.sharpMomentError
  have hL : 0 ≤ L := log_natCast_nonneg R
  have hm1 := cappedLogMoment_succ_error p hp hinj R hR hfull 0
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm1
  change |cappedLogMoment p L 1 - (L ^ 1 / 1 + L ^ 1 * T)| ≤ 2 * e * L ^ 0 at hm1
  have h1 := mul_le_mul_of_nonneg_left ((abs_le.mp hm1).2)
    (show 0 ≤ (5721664 : ℝ) * L ^ 6 by positivity)
  have hm2 := cappedLogMoment_succ_error p hp hinj R hR hfull 1
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm2
  change |cappedLogMoment p L 2 - (L ^ 2 / 2 + L ^ 2 * T)| ≤ 2 * e * L ^ 1 at hm2
  have h2 := mul_le_mul_of_nonneg_left ((abs_le.mp hm2).2)
    (show 0 ≤ ((428544696 / 5) : ℝ) * L ^ 5 by positivity)
  have hm3 := cappedLogMoment_succ_error p hp hinj R hR hfull 2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm3
  change |cappedLogMoment p L 3 - (L ^ 3 / 3 + L ^ 3 * T)| ≤ 2 * e * L ^ 2 at hm3
  have h3 := mul_le_mul_of_nonneg_left ((abs_le.mp hm3).1)
    (show 0 ≤ ((434463325 / 6) : ℝ) * L ^ 4 by positivity)
  have hm4 := cappedLogMoment_succ_error p hp hinj R hR hfull 3
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm4
  change |cappedLogMoment p L 4 - (L ^ 4 / 4 + L ^ 4 * T)| ≤ 2 * e * L ^ 3 at hm4
  have h4 := mul_le_mul_of_nonneg_left ((abs_le.mp hm4).2)
    (show 0 ≤ (49600525 : ℝ) * L ^ 3 by positivity)
  have hm5 := cappedLogMoment_succ_error p hp hinj R hR hfull 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm5
  change |cappedLogMoment p L 5 - (L ^ 5 / 5 + L ^ 5 * T)| ≤ 2 * e * L ^ 4 at hm5
  have h5 := mul_le_mul_of_nonneg_left ((abs_le.mp hm5).1)
    (show 0 ≤ ((147536616 / 5) : ℝ) * L ^ 2 by positivity)
  have hm6 := cappedLogMoment_succ_error p hp hinj R hR hfull 5
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm6
  change |cappedLogMoment p L 6 - (L ^ 6 / 6 + L ^ 6 * T)| ≤ 2 * e * L ^ 5 at hm6
  have h6 := mul_le_mul_of_nonneg_left ((abs_le.mp hm6).2)
    (show 0 ≤ (9217325 : ℝ) * L ^ 1 by positivity)
  have hm7 := cappedLogMoment_succ_error p hp hinj R hR hfull 6
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, one_add_one_eq_two, show (1 : ℝ) + 1 = 2 by norm_num] at hm7
  change |cappedLogMoment p L 7 - (L ^ 7 / 7 + L ^ 7 * T)| ≤ 2 * e * L ^ 6 at hm7
  have h7 := mul_le_mul_of_nonneg_left ((abs_le.mp hm7).1)
    (show 0 ≤ ((239589779 / 70) : ℝ) * L ^ 0 by positivity)
  have he : 0 ≤ e * L ^ 6 := by have := WeightedMertens.sharpMomentError_pos; dsimp [e]; positivity
  rw [hardCubicShiftMain_prime_sum, hardCubicEnergy_eq, hardCubicNorm_eq]
  change 5721664 * L ^ 6 * cappedLogMoment p L 1 +
      (428544696 / 5) * L ^ 5 * cappedLogMoment p L 2 -
      (434463325 / 6) * L ^ 4 * cappedLogMoment p L 3 +
      49600525 * L ^ 3 * cappedLogMoment p L 4 -
      (147536616 / 5) * L ^ 2 * cappedLogMoment p L 5 +
      9217325 * L * cappedLogMoment p L 6 - (239589779 / 70) * cappedLogMoment p L 7 ≤
      (1410547801651 / 44100 + (4715325794 / 105) * T) * L ^ 7 + 1000000000 * e * L ^ 6
  nlinarith only [h1, h2, h3, h4, h5, h6, h7, he]

/-- The leading energy margin is positive at the certified tail budget. All
  finite weighted-discrepancy errors, including their prime sum, remain present. -/
theorem prime_hardCubic_energy_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 2877 / 10000) :
    2000 * log (R : ℝ) ^ 7 -
      (800000000 * additiveNormalizerConstant + 1000000000 * WeightedMertens.sharpMomentError +
        3200000000 * additiveNormalizerConstant * ∑ i, 1 / (p i : ℝ)) * log (R : ℝ) ^ 6 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) := by
  let L := log (R : ℝ)
  let T := ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)
  have hL : 0 ≤ L := log_natCast_nonneg R
  have hn := (abs_le.mp (prime_hardCubic_square_error p hp hinj R hR hfull)).1
  have hd := prime_hardCubic_dirichlet_le p hp hinj R hR hfull
  have hm := prime_hardCubic_shift_main_le p hp hinj R hR hfull
  have hnorm : 0 ≤ hardCubicNorm := by rw [hardCubicNorm_eq]; norm_num
  have ht := mul_le_mul_of_nonneg_left htail (mul_nonneg hnorm (pow_nonneg hL 7))
  have hmargin : (2000 : ℝ) ≤ (1 - 2877 / 10000) * hardCubicNorm - hardCubicEnergy := by
    rw [hardCubic_margin]
    norm_num
  have hg := mul_le_mul_of_nonneg_right hmargin (pow_nonneg hL 7)
  rw [kernelEnergy_weighted _ (prime_marginals p hp)]
  dsimp only [L] at ht hg
  nlinarith only [hn, hd, hm, ht, hg]

#print axioms prime_hardCubic_shift_main_le
#print axioms prime_hardCubic_energy_lower
end Erdos970.FiniteSelberg
