import Submission.MomentReduction

/-! A counterexample to a finite-moment bootstrap even with divisibility
monotonicity. This is not a counterexample to the original conjecture. -/
namespace Erdos322Research.ScalingFiniteMoments

open Finset Erdos322.MomentReduction
set_option Elab.async false

/-- The largest positive integer whose `d`th power divides `n`.
The value at zero is set to zero by the convention for `Nat.divisors`. -/
def maximalPowerDivisor (d n : ℕ) : ℕ :=
  (n.divisors.filter (fun t => t^d ∣ n)).sup id

lemma maximalPowerDivisor_mem (d n : ℕ) (hn : 0 < n) :
    maximalPowerDivisor d n ∈ n.divisors.filter (fun t => t^d ∣ n) := by
  have hne : (n.divisors.filter (fun t => t^d ∣ n)).Nonempty := by
    refine ⟨1,?_⟩
    simp [Nat.mem_divisors,hn.ne']
  have h := Finset.sup_mem_of_nonempty (f := id) hne
  simpa only [Set.image_id] using h

lemma maximalPowerDivisor_pos (d n : ℕ) (hn : 0 < n) :
    0 < maximalPowerDivisor d n := by
  exact Nat.pos_of_mem_divisors (Finset.mem_filter.mp (maximalPowerDivisor_mem d n hn)).1

/-- Monotonicity holds under every positive integral multiple, which is
stronger than the power-scaling monotonicity of representation counts. -/
theorem monotone_under_divisibility (d n m : ℕ) (hm : 0 < m) (hnm : n ∣ m) :
    maximalPowerDivisor d n ≤ maximalPowerDivisor d m := by
  apply Finset.sup_mono
  intro t ht
  obtain ⟨htn,htd⟩ := Finset.mem_filter.mp ht
  refine Finset.mem_filter.mpr ⟨?_,dvd_trans htd hnm⟩
  exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.mem_divisors.mp htn).1 hnm,hm.ne'⟩

/-- The intended peaks are exact, not just lower bounds. -/
theorem maximalPowerDivisor_at_power (d t : ℕ) (hd : 0 < d) (ht : 0 < t) :
    maximalPowerDivisor d (t^d)=t := by
  have hnt : 0 < t^d := pow_pos ht _
  apply le_antisymm
  · have h := (Finset.mem_filter.mp (maximalPowerDivisor_mem d (t^d) hnt)).2
    have hp : maximalPowerDivisor d (t^d)^d ≤ t^d := Nat.le_of_dvd hnt h
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) hd.ne').mp hp
  · apply Finset.le_sup (f := id)
    refine Finset.mem_filter.mpr ⟨?_,dvd_rfl⟩
    exact Nat.mem_divisors.mpr ⟨dvd_pow_self t hd.ne',hnt.ne'⟩

private lemma card_multiples_Icc (N m : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card=N/m := by
  rw [← Nat.card_multiples' N m]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
  omega

/-- A coefficient independent of both the moment order and the spike degree. -/
noncomputable def momentConstant : ℝ := 1+∑' t : ℕ, 1/(t : ℝ)^2

lemma momentConstant_pos : 0 < momentConstant := by
  have h : 0 ≤ ∑' t : ℕ, 1/(t : ℝ)^2 := tsum_nonneg (fun _ => by positivity)
  unfold momentConstant
  linarith

/-- All moments below `d-1` have a linear summatory bound. -/
theorem low_moments_linear (d q N : ℕ) (hqd : q+2 ≤ d) :
    countMoment (maximalPowerDivisor d) q N ≤ momentConstant*(N : ℝ) := by
  classical
  let S := Finset.Icc 1 N
  have hterm (n : ℕ) (hn : n ∈ S) :
      (maximalPowerDivisor d n : ℝ)^q ≤
        ∑ t ∈ S, if t^d ∣ n then (t : ℝ)^q else 0 := by
    have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
    have ht := maximalPowerDivisor_mem d n hn1
    have htd := (Finset.mem_filter.mp ht).2
    have hdiv := Nat.mem_divisors.mp (Finset.mem_filter.mp ht).1
    have htS : maximalPowerDivisor d n ∈ S := by
      apply Finset.mem_Icc.mpr
      exact ⟨maximalPowerDivisor_pos d n hn1,
        (Nat.le_of_dvd hn1 hdiv.1).trans (Finset.mem_Icc.mp hn).2⟩
    have hs := Finset.single_le_sum (s := S)
      (f := fun t : ℕ => if t^d ∣ n then (t : ℝ)^q else 0)
      (fun t _ => by dsimp only; split_ifs <;> positivity) htS
    simpa only [if_pos htd] using hs
  have hratio (t : ℕ) (ht : t ∈ S) : (t : ℝ)^q/(t : ℝ)^d ≤ 1/(t : ℝ)^2 := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
    have htp : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    apply (div_le_div_iff₀ (pow_pos htp _) (pow_pos htp _)).mpr
    rw [← pow_add,one_mul]
    exact pow_le_pow_right₀ ht1 hqd
  have hsum : ∑ t ∈ S, 1/(t : ℝ)^2 ≤ ∑' t : ℕ, 1/(t : ℝ)^2 :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum S
      (fun t _ => by positivity)
  calc
    countMoment (maximalPowerDivisor d) q N ≤
        ∑ n ∈ S, ∑ t ∈ S, if t^d ∣ n then (t : ℝ)^q else 0 :=
      Finset.sum_le_sum hterm
    _ = ∑ t ∈ S, ((N/t^d : ℕ) : ℝ)*(t : ℝ)^q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      change (((S.filter (fun a => t^d ∣ a)).card : ℕ) : ℝ)*(t : ℝ)^q = _
      rw [show (S.filter (fun a => t^d ∣ a)).card=N/t^d from card_multiples_Icc N (t^d)]
    _ ≤ ∑ t ∈ S, (N : ℝ)*((t : ℝ)^q/(t : ℝ)^d) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        ((N/t^d : ℕ) : ℝ)*(t : ℝ)^q ≤
            ((N : ℝ)/((t^d : ℕ) : ℝ))*(t : ℝ)^q :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
        _ = (N : ℝ)*((t : ℝ)^q/(t : ℝ)^d) := by push_cast; ring
    _ ≤ ∑ t ∈ S, (N : ℝ)*(1/(t : ℝ)^2) :=
      Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (hratio t ht) (by positivity))
    _ = (N : ℝ)*(∑ t ∈ S, 1/(t : ℝ)^2) := (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ)*(∑' t : ℕ, 1/(t : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ momentConstant*(N : ℝ) := by unfold momentConstant; nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Divisibility monotonicity does not prevent positive-power peaks. -/
theorem polynomial_peaks (d : ℕ) (hd : 0 < d) :
    ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < (maximalPowerDivisor d n : ℝ)}.Infinite := by
  refine ⟨1/(2*(d : ℝ)),by positivity,?_⟩
  have hinj : Function.Injective (fun t : ℕ => (t+2)^d) := by
    intro a b hab
    have he := Nat.pow_left_injective hd.ne' hab
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨t,rfl⟩
  change (((t+2)^d : ℕ) : ℝ)^(1/(2*(d : ℝ))) < (maximalPowerDivisor d ((t+2)^d) : ℝ)
  rw [maximalPowerDivisor_at_power d (t+2) hd (by omega)]
  have hr : (0 : ℝ) < (t+2 : ℕ) := by positivity
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  have he : (d : ℝ)*(1/(2*(d : ℝ)))=1/2 := by field_simp
  rw [he]
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt
    (by exact_mod_cast (show 1 < t+2 by omega) : (1 : ℝ) < (t+2 : ℕ))
    (by norm_num : (1/2 : ℝ) < 1)

/-- No finite collection of linear moment estimates, even combined with
monotonicity under every positive multiple, implies the desired upper bound. -/
theorem finite_moments_and_scaling_do_not_suffice (Q : ℕ) :
    ∃ r : ℕ → ℕ,
      (∀ n m : ℕ, 0 < m → n ∣ m → r n ≤ r m) ∧
      (∃ C > (0 : ℝ), ∀ q : ℕ, 1 ≤ q → q ≤ Q → ∀ N : ℕ,
        countMoment r q N ≤ C*(N : ℝ)) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (r n : ℝ)}.Infinite) := by
  refine ⟨maximalPowerDivisor (Q+2),monotone_under_divisibility (Q+2),
    ⟨momentConstant,momentConstant_pos,?_⟩,polynomial_peaks (Q+2) (by omega)⟩
  intro q hq hqQ N
  exact low_moments_linear (Q+2) q N (by omega)

end Erdos322Research.ScalingFiniteMoments
