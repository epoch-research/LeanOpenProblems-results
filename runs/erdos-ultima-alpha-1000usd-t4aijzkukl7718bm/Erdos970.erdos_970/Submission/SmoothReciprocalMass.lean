import Submission.SelbergNormalizerAdditive
import Submission.ReciprocalMertens

/-! An elementary lower bound on the finite reciprocal Euler product, obtained
by retaining the smooth part of the harmonic sum through R squared. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def eulerMass (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹

lemma finite_factored_reciprocal_le (P s : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ n ∈ s, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤ eulerMass P := by
  let e (n : s) : Nat.factoredNumbers P := ⟨n.val, hs n.val n.property⟩
  have hi : Function.Injective e := by
    intro n m h
    exact Subtype.ext (congrArg (fun z : Nat.factoredNumbers P => z.val) h)
  have hh := Summable.tsum_le_tsum_of_inj
    (f := fun n : s => 1 / (n.val : ℝ))
    (g := fun n : Nat.factoredNumbers P => 1 / (n.val : ℝ)) e hi
    (fun _ _ => by positivity) (fun _ => le_rfl) (Summable.of_finite)
    (factored_reciprocal_hasSum P hP).summable
  rw [tsum_fintype, sum_coe_sort s (fun n : ℕ => 1 / (n : ℝ)),
    (factored_reciprocal_hasSum P hP).tsum_eq] at hh
  exact hh

lemma reciprocal_multiples_sum (N p : ℕ) (hp : 0 < p) :
    (∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n), 1 / (n : ℝ)) =
      (harmonic (N / p) : ℝ) / p := by
  have he : (Icc 1 N).filter (fun n => p ∣ n) = (Icc 1 (N / p)).image (fun j => p * j) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hpn⟩
      refine ⟨n / p, ⟨Nat.div_pos (Nat.le_of_dvd hn1 hpn) hp, Nat.div_le_div_right hnN⟩, ?_⟩
      exact Nat.mul_div_cancel' hpn
    · rintro ⟨j, ⟨hj1, hjN⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
      exact (Nat.mul_le_mul_left p hjN).trans (Nat.mul_div_le N p)
  rw [he, sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab)]
  have hh : (harmonic (N / p) : ℝ) = ∑ j ∈ Icc 1 (N / p), 1 / (j : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  rw [hh, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [Nat.cast_mul]
  ring

/-- The part of the harmonic sum not supported on primes <=R is charged to
one of its prime factors above R. All finite weights remain nonnegative. -/
theorem harmonic_le_euler_add_tail (R N : ℕ) :
    (harmonic N : ℝ) ≤ eulerMass (R + 1).primesBelow +
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
  have hs := finite_factored_reciprocal_le P S
    (fun p hp => (WeightedMertens.mem_primes.mp hp).1) (fun n hn => (mem_filter.mp hn).2)
  have he (p : ℕ) (hp : p ∈ T) :
      (∑ n ∈ Icc 1 N, if p ∣ n then 1 / (n : ℝ) else 0) = (harmonic (N / p) : ℝ) / p := by
    rw [← sum_filter, reciprocal_multiples_sum N p
      (WeightedMertens.mem_primes.mp (mem_sdiff.mp hp).1).1.pos]
  rw [sum_congr rfl he] at hh
  exact hh.trans (add_le_add hs le_rfl)

lemma reciprocal_tail_eq_interval (R N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow \ (R + 1).primesBelow, 1 / (p : ℝ)) =
      WeightedMertens.reciprocalInterval R N := by
  unfold WeightedMertens.reciprocalInterval
  simp only [Nat.floor_natCast, one_div]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_sdiff, WeightedMertens.mem_primes, mem_filter, mem_Ioc]
  by_cases hp : p.Prime <;> simp only [hp, true_and, false_and, not_true_eq_false,
    not_false_eq_true, and_true, and_false, not_le] <;> tauto

lemma weighted_tail_eq_difference (R N : ℕ) (hRN : R ≤ N) :
    (∑ p ∈ (N + 1).primesBelow \ (R + 1).primesBelow, log (p : ℝ) / p) =
      WeightedMertens.primeSum N - WeightedMertens.primeSum R := by
  have hs : (R + 1).primesBelow ⊆ (N + 1).primesBelow := by
    intro p hp
    obtain ⟨hpp, hpR⟩ := WeightedMertens.mem_primes.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨hpp, hpR.trans hRN⟩
  have h := sum_sdiff (f := fun p : ℕ => log (p : ℝ) / p) hs
  unfold WeightedMertens.primeSum
  linarith

lemma harmonic_quotient_le (N p : ℕ) (hp : 0 < p) (hpN : p ≤ N) :
    (harmonic (N / p) : ℝ) ≤ 1 + log (N : ℝ) - log (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hN : (0 : ℝ) < N := by exact_mod_cast hp.trans_le hpN
  have hx : (1 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hpR).mpr (by simpa only [one_mul] using (Nat.cast_le (α := ℝ)).mpr hpN)
  have h := harmonic_floor_le_one_add_log ((N : ℝ) / p) hx
  rw [Nat.floor_div_natCast, Nat.floor_natCast, log_div hN.ne' hpR.ne'] at h
  linarith

/-- A quantitative Euler-product lower bound in terms of just the two
weighted-Mertens increments. -/
theorem eulerMass_lower_from_tail (R N : ℕ) (hRN : R ≤ N) :
    (harmonic N : ℝ) - (1 + log (N : ℝ)) * WeightedMertens.reciprocalInterval R N +
      (WeightedMertens.primeSum N - WeightedMertens.primeSum R) ≤
      eulerMass (R + 1).primesBelow := by
  have h := harmonic_le_euler_add_tail R N
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

#print axioms harmonic_le_euler_add_tail
#print axioms eulerMass_lower_from_tail
end Erdos970.FiniteSelberg
