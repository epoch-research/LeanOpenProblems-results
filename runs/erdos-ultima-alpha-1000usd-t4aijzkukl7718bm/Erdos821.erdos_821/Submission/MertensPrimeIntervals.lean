import Submission.MertensAbel
import Submission.ReciprocalTotientTwo

/-!
# Sharp logarithmic prime mass on power-scale intervals

The reciprocal-prime mass between 2^(a*m) and 2^(b*m) tends to log(b/a).
This is an elementary Mertens estimate, not an assertion about shifted primes.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
set_option maxHeartbeats 3000000

noncomputable def primeLogCoeff (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ)/(n : ℝ) else 0

noncomputable def primeReciprocalInterval (A B : ℕ) : ℝ :=
  ∑ p ∈ Ioc A B with p.Prime, 1/(p : ℝ)

noncomputable def primeTotientInterval (A B : ℕ) : ℝ :=
  ∑ p ∈ Ioc A B with p.Prime, 1/(p.totient : ℝ)

lemma sum_primeLogCoeff (N : ℕ) :
    (∑ n ∈ Icc 0 N, primeLogCoeff n) = primeLogMass N := by
  have hs : (Icc 0 N).filter Nat.Prime = (N+1).primesBelow := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by have := (mem_Icc.mp hpI).2; omega,hpr⟩
    · intro hp
      obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,hpr⟩
  simp only [primeLogCoeff]
  rw [← sum_filter, hs]
  rfl

lemma sum_primeLogCoeff_div_log (A B : ℕ) :
    (∑ p ∈ Ioc A B, primeLogCoeff p/Real.log p) = primeReciprocalInterval A B := by
  rw [primeReciprocalInterval, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hpr : p.Prime
  · simp only [primeLogCoeff, hpr, if_true]
    have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hpr.one_lt)).ne'
    field_simp
  · simp [primeLogCoeff, hpr]

/-- The interval error is O(1/log A), uniformly in its upper endpoint B. -/
theorem exists_primeReciprocalInterval_log_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      |primeReciprocalInterval A B-Real.log (Real.log B/Real.log A)| ≤ D/Real.log A := by
  obtain ⟨C,hC,HC⟩ := exists_primeLogMass_log_bound
  refine ⟨2*(C+1), by positivity, ?_⟩
  intro A B hA hAB
  have h := reciprocal_log_weight_sum_bound primeLogCoeff A B hA hAB (C+1) (by positivity) (by
    intro x hx
    rw [sum_primeLogCoeff]
    exact primeLogMass_floor_log_bound C HC x
      ((by exact_mod_cast hA : (2 : ℝ) ≤ A).trans hx.1))
  simpa only [sum_primeLogCoeff_div_log] using h

lemma primeTotientInterval_sub_nonneg (A B : ℕ) :
    0 ≤ primeTotientInterval A B-primeReciprocalInterval A B := by
  apply sub_nonneg.mpr
  apply sum_le_sum
  intro p hp
  have hpr := (mem_filter.mp hp).2
  apply div_le_div_of_nonneg_left (by norm_num)
    (by exact_mod_cast Nat.totient_pos.mpr hpr.pos)
  exact_mod_cast Nat.totient_le p

lemma primeTotientInterval_sub_le (A B : ℕ) (hA : 1 ≤ A) :
    primeTotientInterval A B-primeReciprocalInterval A B ≤ 1/(A : ℝ) := by
  unfold primeTotientInterval primeReciprocalInterval
  rw [← sum_sub_distrib]
  have he (p : ℕ) (hp : p ∈ (Ioc A B).filter Nat.Prime) :
      1/(p.totient : ℝ)-1/(p : ℝ) = 1/((p : ℝ)*((p : ℝ)-1)) := by
    have hpr := (mem_filter.mp hp).2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
    have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hpr.one_lt))
    rw [Nat.totient_prime hpr, Nat.cast_sub hpr.one_lt.le, Nat.cast_one]
    field_simp
    ring
  rw [sum_congr rfl he]
  apply le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp _ => ?_))
    (by
      have hs : Ioc A B = Icc (A+1) B := by ext n; simp only [mem_Ioc,mem_Icc]; omega
      rw [hs]
      exact Sieve.sum_reciprocal_successive_tail A B hA)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (hA.trans (mem_Ioc.mp hp).1.le)
  exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

lemma log_power_scale_ratio (a b m : ℕ) (ha : 1 ≤ a) (hm : 1 ≤ m) :
    Real.log ((2^(b*m) : ℕ) : ℝ)/Real.log ((2^(a*m) : ℕ) : ℝ) = (b : ℝ)/a := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
  field_simp

lemma tendsto_power_scale_nat (a : ℕ) (ha : 1 ≤ a) :
    Tendsto (fun m : ℕ => (2 : ℕ)^(a*m)) atTop atTop := by
  apply (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ)<2)).comp
  exact tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m ha) tendsto_id

/-- Reciprocal prime mass has the exact logarithmic interval limit. -/
theorem tendsto_primeReciprocalInterval_power (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun m : ℕ => primeReciprocalInterval (2^(a*m)) (2^(b*m))) atTop
      (𝓝 (Real.log ((b : ℝ)/a))) := by
  obtain ⟨D,hD,HD⟩ := exists_primeReciprocalInterval_log_bound
  have hlim := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_power_scale_nat a ha))).const_div_atTop D
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hp : 2 ≤ (2 : ℕ)^(a*m) := Nat.one_lt_pow (Nat.ne_of_gt (Nat.mul_pos ha hm)) (by decide)
  have hpow : (2 : ℕ)^(a*m) ≤ 2^(b*m) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right m hab)
  have hh := HD (2^(a*m)) (2^(b*m)) hp hpow
  rw [log_power_scale_ratio a b m ha hm] at hh
  simpa only [Real.norm_eq_abs] using hh

/-- Replacing 1/p by 1/phi(p) does not change the interval limit. -/
theorem tendsto_primeTotientInterval_power (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun m : ℕ => primeTotientInterval (2^(a*m)) (2^(b*m))) atTop
      (𝓝 (Real.log ((b : ℝ)/a))) := by
  have hzero : Tendsto (fun m : ℕ => primeTotientInterval (2^(a*m)) (2^(b*m))-
      primeReciprocalInterval (2^(a*m)) (2^(b*m))) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => primeTotientInterval_sub_nonneg _ _)
      (fun m => primeTotientInterval_sub_le _ _ (Nat.one_le_pow _ _ (by decide)))
    exact (tendsto_natCast_atTop_atTop.comp (tendsto_power_scale_nat a ha)).const_div_atTop 1
  have hsum := hzero.add (tendsto_primeReciprocalInterval_power a b ha hab)
  simpa only [sub_add_cancel, zero_add] using hsum

end Erdos821
