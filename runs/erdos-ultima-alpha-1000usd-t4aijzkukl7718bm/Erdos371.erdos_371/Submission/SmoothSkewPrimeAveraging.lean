import Submission.SmoothCutoffSkew
import Submission.HarmonicCofactorCutoff

/-! A uniform small-prime averaging identity for the actual smooth-cutoff
skew. The approximation error tends to zero, but the remaining averages
along `p*m+1` are not asserted to cancel. -/

namespace Erdos371

open Finset Filter
open scoped Topology

noncomputable def primeWeightedSum (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, primeDivCount S (n+1) * a (n+1)

/-- The elementary second-moment estimate applies uniformly to every bounded
real observable, including observables depending on the averaging endpoint. -/
theorem primeWeightedSum_error_sq (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ n, |a n| ≤ 1) :
    (primeReciprocalSum S * (∑ n ∈ range N, a (n+1)) - primeWeightedSum S a N)^2 ≤
      N * (N * primeReciprocalSum S + 2 * primeReciprocalSum S * S.card) := by
  have he : primeReciprocalSum S * (∑ n ∈ range N, a (n+1)) - primeWeightedSum S a N =
      ∑ n ∈ range N, a (n+1) * (primeReciprocalSum S - primeDivCount S (n+1)) := by
    simp only [primeWeightedSum, mul_sub, sum_sub_distrib, ← sum_mul]
    simp only [mul_comm]
  rw [he]
  have hcs := sum_mul_sq_le_sq_mul_sq (range N) (fun n => a (n+1))
    (fun n => primeReciprocalSum S - primeDivCount S (n+1))
  have ha2 : (∑ n ∈ range N, (a (n+1))^2) ≤ N := by
    calc
      _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum fun n _ => by
        have h := pow_le_pow_left₀ (abs_nonneg (a (n+1))) (ha (n+1)) 2
        simpa only [sq_abs, one_pow] using h
      _ = _ := by simp
  have hv : (∑ n ∈ range N, (primeReciprocalSum S - primeDivCount S (n+1))^2) ≤
      N * primeReciprocalSum S + 2 * primeReciprocalSum S * S.card := by
    simpa only [sub_sq_comm] using primeDivCount_variance_upper S N hS
  exact hcs.trans (mul_le_mul ha2 hv (by positivity) (Nat.cast_nonneg N))

/-- Normalized Turán averaging, with a bound independent of the observable. -/
theorem primeWeightedSum_error_bound (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ n, |a n| ≤ 1)
    (hc : S.card ≤ N) (hN : 0 < N) (hH : 0 < primeReciprocalSum S) :
    |(∑ n ∈ range N, a (n+1)) / N - primeWeightedSum S a N / (N * primeReciprocalSum S)| ≤
      Real.sqrt (3 / primeReciprocalSum S) := by
  let H := primeReciprocalSum S
  let A := ∑ n ∈ range N, a (n+1)
  let W := primeWeightedSum S a N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : (S.card : ℝ) ≤ N := by exact_mod_cast hc
  have he : (H*A-W)^2 ≤ 3*(N : ℝ)^2*H := by
    have hh := primeWeightedSum_error_sq S a N hS ha
    have hh' := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 2*H by dsimp [H]; positivity)
    change (H*A-W)^2 ≤ (N : ℝ)*((N : ℝ)*H+2*H*S.card) at hh
    nlinarith
  change |A / N - W / (N*H)| ≤ Real.sqrt (3/H)
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  have hHN : (N : ℝ)*H ≠ 0 := mul_ne_zero hN'.ne' hH.ne'
  have hH0 : H ≠ 0 := hH.ne'
  have hid : A / N - W / (N*H) = (H*A-W)/(N*H) := by
    field_simp
  rw [hid, div_pow]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hHN)).mpr
  have hid' : 3 / H * ((N : ℝ)*H)^2 = 3*(N : ℝ)^2*H := by
    field_simp
  rwa [hid']

lemma sum_positive_multiples (a : ℕ → ℝ) (p N : ℕ) (hp : 0 < p) :
    (∑ n ∈ range N, if p ∣ n+1 then a (n+1) else 0) =
      ∑ m ∈ Icc 1 (N/p), a (p*m) := by
  classical
  rw [← sum_filter]
  symm
  apply sum_bij (fun m _ => p*m-1)
  · intro m hm
    obtain ⟨hm0, hmN⟩ := mem_Icc.mp hm
    have hpm : p*m ≤ N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmN
    have hpos : 0 < p*m := Nat.mul_pos hp (by omega)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p*m)]
      exact Nat.dvd_mul_right p m⟩
  · intro m hm k hk he
    have hmpos : 0 < p*m := Nat.mul_pos hp (by have := (mem_Icc.mp hm).1; omega)
    have hkpos : 0 < p*k := Nat.mul_pos hp (by have := (mem_Icc.mp hk).1; omega)
    have he' : p*m = p*k := by omega
    exact Nat.eq_of_mul_eq_mul_left hp he'
  · intro n hn
    obtain ⟨hnN, hpn⟩ := mem_filter.mp hn
    have hmul := Nat.mul_div_cancel' hpn
    have hm0 := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < n+1) hpn) hp
    refine ⟨(n+1)/p, mem_Icc.mpr ⟨by omega, Nat.div_le_div_right (by
      have := mem_range.mp hnN
      omega)⟩, ?_⟩
    omega
  · intro m hm
    have hpos : 1 ≤ p*m := Nat.mul_pos hp (by have := (mem_Icc.mp hm).1; omega)
    rw [Nat.sub_add_cancel hpos]

lemma primeWeightedSum_eq_progressions (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) :
    primeWeightedSum S a N = ∑ p ∈ S, ∑ m ∈ Icc 1 (N/p), a (p*m) := by
  unfold primeWeightedSum primeDivCount
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have he (n : ℕ) : (if p ∣ n+1 then (1 : ℝ) else 0) * a (n+1) =
      if p ∣ n+1 then a (n+1) else 0 := by split_ifs <;> simp
  simp_rw [he]
  exact sum_positive_multiples a p N (hS p hp)

lemma smoothIndicator_mul_small (B p m : ℕ) (hp : 0 < p)
    (hm : 0 < m) (hpB : p ≤ B) :
    smoothIndicator B (p*m) = smoothIndicator B m := by
  unfold smoothIndicator
  simp only [Nat.maxPrimeFac_mul hp.ne' hm.ne', max_le_iff,
    Nat.maxPrimeFac_le.trans hpB, true_and]

noncomputable def smallPrimeSkewAverage (S : Finset ℕ) (B C N : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ m ∈ Icc 1 (N/p),
    (smoothIndicator B m * smoothIndicator C (p*m+1) -
      smoothIndicator C m * smoothIndicator B (p*m+1))

lemma smoothSkewPoint_abs_le_one (B C n : ℕ) :
    |smoothIndicator B n * smoothIndicator C (n+1) -
      smoothIndicator C n * smoothIndicator B (n+1)| ≤ 1 := by
  unfold smoothIndicator
  split_ifs <;> norm_num

lemma smallPrimeSkewAverage_eq_weighted (S : Finset ℕ) (B C N : ℕ)
    (hS : ∀ p ∈ S, 0 < p ∧ p ≤ B ∧ p ≤ C) :
    smallPrimeSkewAverage S B C N = primeWeightedSum S
      (fun n => smoothIndicator B n * smoothIndicator C (n+1) -
        smoothIndicator C n * smoothIndicator B (n+1)) N := by
  rw [primeWeightedSum_eq_progressions S _ N (fun p hp => (hS p hp).1)]
  unfold smallPrimeSkewAverage
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by have := (mem_Icc.mp hm).1; omega
  rw [smoothIndicator_mul_small B p m (hS p hp).1 hm0 (hS p hp).2.1,
    smoothIndicator_mul_small C p m (hS p hp).1 hm0 (hS p hp).2.2]

/-- A finite, uniform approximation to the signed smooth-cutoff skew by
small-prime linear-form averages. Each inner sum retains its own endpoint. -/
theorem smoothCutoffSkew_prime_average_bound (S : Finset ℕ) (B C N : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ B ∧ p ≤ C)
    (hc : S.card ≤ N) (hN : 0 < N) (hH : 0 < primeReciprocalSum S) :
    |smoothCutoffSkew B C N / N - smallPrimeSkewAverage S B C N / (N * primeReciprocalSum S)| ≤
      Real.sqrt (3 / primeReciprocalSum S) := by
  rw [smallPrimeSkewAverage_eq_weighted S B C N
    (fun p hp => ⟨(hS p hp).1.pos, (hS p hp).2⟩)]
  exact primeWeightedSum_error_bound S _ N (fun p hp => (hS p hp).1)
    (smoothSkewPoint_abs_le_one B C) hc hN hH

lemma primesBelow_succ_card_le (K : ℕ) : (K+1).primesBelow.card ≤ K := by
  have hs : (K+1).primesBelow ⊆ Icc 1 K := by
    intro p hp
    obtain ⟨hpK, hp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hp.one_le, by omega⟩
  simpa using card_le_card hs

/-- The replacement error is `o(N)` uniformly in both moving cutoffs.
This does not assert cancellation of the remaining linear-form average. -/
theorem smoothCutoffSkew_prime_average_error_tendsto (B C K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop)
    (hcut : ∀ᶠ N : ℕ in atTop, K N ≤ B N ∧ K N ≤ C N ∧ K N ≤ N) :
    Tendsto (fun N => smoothCutoffSkew (B N) (C N) N / N -
      smallPrimeSkewAverage (K N+1).primesBelow (B N) (C N) N /
        (N * primeHarmonic (K N))) atTop (nhds 0) := by
  have hH := primeHarmonic_atTop.comp hK
  have ht := (hH.inv_tendsto_atTop.const_mul (3 : ℝ)).sqrt
  simp only [mul_zero, Real.sqrt_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hcut, hH.eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (0 : ℕ)]
    with N hcut hHN hN
  rw [Real.norm_eq_abs]
  have hS (p : ℕ) (hp : p ∈ (K N+1).primesBelow) :
      p.Prime ∧ p ≤ B N ∧ p ≤ C N := by
    obtain ⟨hpK, hp⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hp, (by omega : p ≤ K N).trans hcut.1,
      (by omega : p ≤ K N).trans hcut.2.1⟩
  simpa only [primeHarmonic, div_eq_mul_inv, Pi.inv_apply] using
    smoothCutoffSkew_prime_average_bound (K N+1).primesBelow (B N) (C N) N hS
      ((primesBelow_succ_card_le (K N)).trans hcut.2.2) hN hHN

#print axioms primeWeightedSum_error_bound
#print axioms smoothCutoffSkew_prime_average_bound
#print axioms smoothCutoffSkew_prime_average_error_tendsto

end Erdos371
