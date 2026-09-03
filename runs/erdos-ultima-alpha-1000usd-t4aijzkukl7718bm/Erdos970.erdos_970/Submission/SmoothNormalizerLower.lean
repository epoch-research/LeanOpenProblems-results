import Submission.SmoothReciprocalMass

/-! Lower Selberg normalizer bounds beyond the prime cutoff. The smooth
harmonic terms are retained, and nonsmooth terms are charged to large prime
divisors. These estimates do not establish a Jacobsthal growth bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real

theorem harmonic_le_normalizer_add_tail (R N : ℕ) :
    (harmonic N : ℝ) ≤ primeNormalizer (R + 1).primesBelow N +
      ∑ p ∈ (N + 1).primesBelow \ (R + 1).primesBelow,
        (harmonic (N / p) : ℝ) / p := by
  classical
  let P := (R + 1).primesBelow
  let T := (N + 1).primesBelow \ P
  let S := (Icc 1 N).filter (fun n => n ∈ Nat.factoredNumbers P)
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      1 / (n : ℝ) ≤ (if n ∈ Nat.factoredNumbers P then 1 / (n : ℝ) else 0) +
        ∑ p ∈ T, if p ∣ n then 1 / (n : ℝ) else 0 := by
    by_cases hs : n ∈ Nat.factoredNumbers P
    · rw [if_pos hs]
      exact le_add_of_nonneg_right (sum_nonneg (fun p _ => by split_ifs <;> positivity))
    · rw [if_neg hs, zero_add]
      have hnot : ¬n.primeFactors ⊆ P := by
        intro h
        exact hs (Nat.mem_factoredNumbers_of_primeFactors_subset (by have := (mem_Icc.mp hn).1; omega) h)
      obtain ⟨p, hpn, hpP⟩ := not_subset.mp hnot
      obtain ⟨hpp, hpd, hn0⟩ := Nat.mem_primeFactors.mp hpn
      have hpN := (Nat.le_of_dvd (by have := (mem_Icc.mp hn).1; omega) hpd).trans (mem_Icc.mp hn).2
      have hpT : p ∈ T := mem_sdiff.mpr ⟨WeightedMertens.mem_primes.mpr ⟨hpp, hpN⟩, hpP⟩
      have h := single_le_sum (s := T) (f := fun p => if p ∣ n then 1 / (n : ℝ) else 0)
        (fun p _ => by dsimp only; split_ifs <;> positivity) hpT
      simpa only [hpd, if_true] using h
  have hh := sum_le_sum hpoint
  rw [sum_add_distrib, sum_comm] at hh
  have hH : (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  rw [hH, ← sum_filter] at hh
  have hs := reciprocal_sum_le_smallDivisorFamily P S
    (fun p hp => (WeightedMertens.mem_primes.mp hp).1) N (fun n hn => by
      obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
      exact ⟨(mem_Icc.mp hnI).1, (mem_Icc.mp hnI).2,
        Nat.primeFactors_subset_of_mem_factoredNumbers hnP⟩)
  change (∑ n ∈ S, 1 / (n : ℝ)) ≤ primeNormalizer P N at hs
  have he (p : ℕ) (hp : p ∈ T) :
      (∑ n ∈ Icc 1 N, if p ∣ n then 1 / (n : ℝ) else 0) = (harmonic (N / p) : ℝ) / p := by
    rw [← sum_filter, reciprocal_multiples_sum N p
      (WeightedMertens.mem_primes.mp (mem_sdiff.mp hp).1).1.pos]
  rw [sum_congr rfl he] at hh
  exact hh.trans (add_le_add hs le_rfl)

theorem primeNormalizer_lower_from_tail (R N : ℕ) (hRN : R ≤ N) :
    (harmonic N : ℝ) - (1 + log (N : ℝ)) * WeightedMertens.reciprocalInterval R N +
      (WeightedMertens.primeSum N - WeightedMertens.primeSum R) ≤
      primeNormalizer (R + 1).primesBelow N := by
  have h := harmonic_le_normalizer_add_tail R N
  have ht : (∑ p ∈ (N + 1).primesBelow \ (R + 1).primesBelow,
      (harmonic (N / p) : ℝ) / p) ≤
      (1 + log (N : ℝ)) * WeightedMertens.reciprocalInterval R N -
      (WeightedMertens.primeSum N - WeightedMertens.primeSum R) := by
    rw [← reciprocal_tail_eq_interval, ← weighted_tail_eq_difference R N hRN,
      mul_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hpN⟩ := WeightedMertens.mem_primes.mp (mem_sdiff.mp hp).1
    have hh := div_le_div_of_nonneg_right (harmonic_quotient_le N p hpp.pos hpN) (Nat.cast_nonneg p)
    convert hh using 1 <;> ring
  linarith


/-- For cutoffs with log N = u*log R and 1<=u<=3, a union bound on omitted
prime divisors gives the explicit shape 2u-1-u*log u, with absolute error. -/
theorem primeNormalizer_lower_through_cube (R N : ℕ) (hR : 2 ≤ R) (hRN : R ≤ N)
    (hL : 1 ≤ log (R : ℝ)) (u : ℝ) (hu : 1 ≤ u) (hu3 : u ≤ 3)
    (hlog : log (N : ℝ) = u * log (R : ℝ)) :
    (2 * u - 1 - u * log u) * log (R : ℝ) -
      12 * (WeightedMertens.boundConstant + 1) ≤ primeNormalizer (R + 1).primesBelow N := by
  let C := WeightedMertens.boundConstant
  let A := log (R : ℝ)
  let B := log (N : ℝ)
  have hC : 0 < C := WeightedMertens.boundConstant_pos
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hu0 : 0 < u := by linarith
  have huLog : log u ≤ 2 := by
    have hh := log_le_sub_one_of_pos hu0
    linarith
  have hlogs : log (log (N : ℝ)) - log (log (R : ℝ)) = log u := by
    rw [hlog, log_mul hu0.ne' hA.ne']
    ring
  have ht := (abs_le.mp (WeightedMertens.abs_reciprocalInterval_sub_loglog
    (a := (R : ℝ)) (b := (N : ℝ)) (by exact_mod_cast hR) (by exact_mod_cast hRN))).2
  rw [hlogs] at ht
  change WeightedMertens.reciprocalInterval R N - log u ≤ 2 * (C + 1) / A at ht
  have hmult := mul_le_mul_of_nonneg_left ht (show 0 ≤ 1 + B by linarith)
  have hfrac : (1 + B) * (2 * (C + 1) / A) ≤ 8 * (C + 1) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hA).mpr
    have hB3 : B ≤ 3 * A := by
      change log (N : ℝ) ≤ 3 * log (R : ℝ)
      rw [hlog]
      exact mul_le_mul_of_nonneg_right hu3 hA.le
    change 1 ≤ A at hL
    nlinarith only [mul_nonneg (by linarith only [hC] : 0 ≤ C + 1)
      (by linarith only [hB3, hL] : 0 ≤ 4 * A - (1 + B))]
  have hr := (abs_le.mp (WeightedMertens.abs_primeSum_sub_log R (by omega))).2
  have hn := (abs_le.mp (WeightedMertens.abs_primeSum_sub_log N (by omega))).1
  have hH := log_le_harmonic_floor (N : ℝ) (by positivity)
  rw [Nat.floor_natCast] at hH
  have hlo := primeNormalizer_lower_from_tail R N hRN
  change WeightedMertens.primeSum R - A ≤ C at hr
  change -C ≤ WeightedMertens.primeSum N - B at hn
  change B ≤ (harmonic N : ℝ) at hH
  change (harmonic N : ℝ) - (1 + B) * WeightedMertens.reciprocalInterval R N +
    (WeightedMertens.primeSum N - WeightedMertens.primeSum R) ≤ _ at hlo
  have hbnd : 2 * B - A - B * log u - 12 * (C + 1) ≤
      primeNormalizer (R + 1).primesBelow N := by
    nlinarith only [hlo, hr, hn, hH, hmult, hfrac, huLog, hC]
  change (2 * u - 1 - u * log u) * A - 12 * (C + 1) ≤ _
  have he : B = u * A := hlog
  rw [he] at hbnd
  convert hbnd using 1 <;> ring

#print axioms harmonic_le_normalizer_add_tail
#print axioms primeNormalizer_lower_from_tail
#print axioms primeNormalizer_lower_through_cube
end Erdos970.FiniteSelberg
