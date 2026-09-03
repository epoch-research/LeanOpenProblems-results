import Submission.FiniteLayerCake

/-! Sharp leading coefficients for the second and third logarithmic prime
moments, deduced from the elementary weighted Mertens estimate. -/
namespace Erdos970.WeightedMertens
open Finset Real Erdos970.FiniteSelberg

lemma abs_realPrimeSum_sub_log_one (x : ℝ) (hx : 1 ≤ x) :
    |realPrimeSum x - log x| ≤ boundConstant + 1 := by
  by_cases hx2 : 2 ≤ x
  · exact abs_realPrimeSum_sub_log x hx2
  · have hf : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr (by norm_num; exact ⟨hx, by linarith⟩)
    have hs : realPrimeSum x = 0 := by
      rw [realPrimeSum, hf]
      simp only [primeSum, show (1 + 1 : ℕ).primesBelow = ∅ from by decide, sum_empty]
    rw [hs, zero_sub, abs_neg, abs_of_nonneg (log_nonneg hx)]
    have hh := log_le_sub_one_of_pos (by linarith : 0 < x)
    linarith [boundConstant_pos]

noncomputable def sharpMomentError : ℝ := boundConstant + 2

lemma sharpMomentError_pos : 0 < sharpMomentError := by
  unfold sharpMomentError
  linarith [boundConstant_pos]

noncomputable def initialPrimeCumulative (R : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ ((R + 1).primesBelow.filter (fun p : ℕ => log (p : ℝ) < t)), log (p : ℝ) / (p : ℝ)

lemma initialPrimeCumulative_nonneg (R : ℕ) (t : ℝ) :
    0 ≤ initialPrimeCumulative R t :=
  sum_nonneg (fun p _ => div_nonneg (log_natCast_nonneg p) (Nat.cast_nonneg p))

lemma initialPrimeCumulative_error (R : ℕ) (hR : 0 < R) (t : ℝ)
    (ht : 0 ≤ t) (htR : t ≤ log R) :
    |initialPrimeCumulative R t - t| ≤ sharpMomentError := by
  have hu : initialPrimeCumulative R t ≤ realPrimeSum (exp t) := by
    unfold initialPrimeCumulative realPrimeSum primeSum
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpR, hpt⟩ := mem_filter.mp hp
      have hpp := (mem_primes.mp hpR).1
      apply mem_primes.mpr
      refine ⟨hpp, Nat.le_floor ?_⟩
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      rw [← exp_log hp0]
      exact exp_le_exp.mpr hpt.le
    · intro p hp hn
      exact div_nonneg (log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hu' := (abs_le.mp (abs_realPrimeSum_sub_log_one (exp t) (one_le_exp ht))).2
  rw [log_exp] at hu'
  have hlo : t - sharpMomentError ≤ initialPrimeCumulative R t := by
    by_cases ht1 : t ≤ 1
    · have hh := initialPrimeCumulative_nonneg R t
      unfold sharpMomentError
      linarith [boundConstant_pos]
    · have hcut : ⌊exp (t - 1)⌋₊ ≤ R := by
        have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
        have he : exp (t - 1) ≤ (R : ℝ) := by
          rw [← exp_log hR0]
          exact exp_le_exp.mpr (by linarith)
        simpa only [Nat.floor_natCast] using Nat.floor_le_floor he
      have hs : realPrimeSum (exp (t - 1)) ≤ initialPrimeCumulative R t := by
        unfold realPrimeSum primeSum initialPrimeCumulative
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpp, hpcut⟩ := mem_primes.mp hp
          refine mem_filter.mpr ⟨mem_primes.mpr ⟨hpp, hpcut.trans hcut⟩, ?_⟩
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hpe : (p : ℝ) ≤ exp (t - 1) :=
            (by exact_mod_cast hpcut : (p : ℝ) ≤ ⌊exp (t - 1)⌋₊).trans (Nat.floor_le (exp_pos _).le)
          have hh := log_le_log hp0 hpe
          rw [log_exp] at hh
          linarith
        · intro p hp hn
          exact div_nonneg (log_natCast_nonneg p) (Nat.cast_nonneg p)
      have hh := (abs_le.mp (abs_realPrimeSum_sub_log_one (exp (t - 1))
        (one_le_exp (by linarith)))).1
      rw [log_exp] at hh
      unfold sharpMomentError
      linarith
  rw [abs_le]
  unfold sharpMomentError at *
  constructor <;> linarith

lemma initialPrimeCumulative_eq (R : ℕ) (t : ℝ) :
    cumulativeMass (fun p : (R + 1).primesBelow => log (p.val : ℝ) / p.val)
      (fun p : (R + 1).primesBelow => log (p.val : ℝ)) t = initialPrimeCumulative R t := by
  simp only [cumulativeMass, initialPrimeCumulative, sum_filter]
  exact sum_coe_sort _ (fun p : ℕ => if log (p : ℝ) < t then log (p : ℝ) / p else 0)

/-- The leading constants are 1/2 and 1/3, with uniform lower-order errors. -/
theorem prime_second_third_log_moments (R : ℕ) (hR : 0 < R) :
    |(∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 2 / p) - log (R : ℝ) ^ 2 / 2| ≤
        2 * sharpMomentError * log R ∧
    |(∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 3 / p) - log (R : ℝ) ^ 3 / 3| ≤
        4 * sharpMomentError * log R ^ 2 := by
  let P := (R + 1).primesBelow
  have ha (p : P) : 0 ≤ log (p.val : ℝ) ∧ log (p.val : ℝ) ≤ log R := by
    obtain ⟨hpp, hpR⟩ := mem_primes.mp p.property
    exact ⟨log_natCast_nonneg _, log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpR)⟩
  have htotal : |(∑ p : P, log (p.val : ℝ) / p.val) - log (R : ℝ)| ≤ sharpMomentError := by
    have hs : (∑ p : P, log (p.val : ℝ) / p.val) = primeSum R := sum_coe_sort P (fun p : ℕ => log (p : ℝ) / p)
    rw [hs]
    exact (abs_primeSum_sub_log R hR).trans (by unfold sharpMomentError; linarith)
  have hh := cumulative_moments (fun p : P => log (p.val : ℝ) / p.val)
    (fun p : P => log (p.val : ℝ)) (log R) sharpMomentError (log_natCast_nonneg R) ha htotal
    (fun t ht => by rw [initialPrimeCumulative_eq]; exact initialPrimeCumulative_error R hR t ht.1 ht.2)
  have hs₂ : (∑ p : P, (log (p.val : ℝ) / p.val) * log (p.val : ℝ)) =
      ∑ p ∈ P, log (p : ℝ) ^ 2 / p := by
    rw [sum_coe_sort P (fun p : ℕ => (log (p : ℝ) / p) * log p)]
    apply sum_congr rfl
    intro p hp
    ring
  have hs₃ : (∑ p : P, (log (p.val : ℝ) / p.val) * log (p.val : ℝ) ^ 2) =
      ∑ p ∈ P, log (p : ℝ) ^ 3 / p := by
    rw [sum_coe_sort P (fun p : ℕ => (log (p : ℝ) / p) * log p ^ 2)]
    apply sum_congr rfl
    intro p hp
    ring
  rw [hs₂, hs₃] at hh
  exact hh

#print axioms initialPrimeCumulative_error
#print axioms prime_second_third_log_moments
end Erdos970.WeightedMertens
