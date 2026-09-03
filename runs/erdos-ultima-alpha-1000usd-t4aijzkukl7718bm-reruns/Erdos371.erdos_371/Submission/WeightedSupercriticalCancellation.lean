import FormalConjecturesUtil
import Submission.WeightedPrimeCrossCancellation
import Submission.GlobalSupercriticalCutoff

/-! Signed logarithmic-weight cancellation for supercritical prime pairs.
The weights vary with the input and can vanish; this is not a proof of
unweighted largest-prime comparison balance. -/

namespace Erdos371WeightedSupercriticalCancellation

open Finset Filter Erdos371WeightedPrimeCrossCancellation
open Erdos371GlobalSupercriticalCutoff
open Erdos371SubcriticalPrimePairCancellation (count)
open scoped Topology

def lowPairs (N n : ℕ) : Finset (ℕ × ℕ) :=
  (n.primeFactors.product (n+1).primeFactors).filter fun z => z.1*z.2 ≤ N

lemma lowPairs_eq (N n : ℕ) :
    lowPairs N n = (orderedPairs N).filter (fun z => z.1 ∣ n ∧ z.2 ∣ n+1) := by
  ext ⟨p,q⟩
  constructor
  · intro hz
    obtain ⟨hz,hN⟩ := mem_filter.mp hz
    obtain ⟨hp,hq⟩ := mem_product.mp hz
    obtain ⟨hpprime,hpn,hn0⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨hqprime,hqn,_⟩ := Nat.mem_primeFactors.mp hq
    have hpq : p ≠ q := by
      intro he
      subst q
      exact hpprime.not_dvd_one (by simpa using Nat.dvd_sub hqn hpn)
    exact mem_filter.mpr ⟨mem_orderedPairs.mpr ⟨hpprime,hqprime,hpq,hN⟩,hpn,hqn⟩
  · intro hz
    obtain ⟨hz,hpn,hqn⟩ := mem_filter.mp hz
    obtain ⟨hp,hq,hpq,hN⟩ := mem_orderedPairs.mp hz
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      exact hq.not_dvd_one (by simpa using hqn)
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp,hpn,hn0⟩,
       Nat.mem_primeFactors.mpr ⟨hq,hqn,by omega⟩⟩,hN⟩

lemma sum_lowPairs (N : ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ p q, c q p = -c p q) :
    (∑ n ∈ range N, ∑ z ∈ lowPairs N n, c z.1 z.2) = subcritical N c := by
  simp only [lowPairs_eq, sum_filter]
  rw [sum_comm]
  have he : (∑ z ∈ orderedPairs N, ∑ n ∈ range N,
      if z.1 ∣ n ∧ z.2 ∣ n+1 then c z.1 z.2 else 0) =
      ∑ z ∈ orderedPairs N, c z.1 z.2 * (count z.1 z.2 N : ℝ) := by
    apply sum_congr rfl
    intro z hz
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rfl
  rw [he, orderedPairs, sum_union (ordered_disjoint N),
    sum_image Prod.swap_injective.injOn, ← sum_add_distrib]
  unfold subcritical
  apply sum_congr rfl
  rintro ⟨p,q⟩ hz
  dsimp only [Prod.swap]
  rw [hc p q]
  ring

lemma coefficient_swap (N : ℕ) (f : ℕ → ℝ) (p q : ℕ) :
    coefficient N f q p = -coefficient N f p q := by
  unfold coefficient
  ring

noncomputable def supercritical (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ z ∈ globalPairs N n, coefficient N f z.1 z.2

lemma cross_split (N : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    cross N f n = (∑ z ∈ lowPairs N n, coefficient N f z.1 z.2) + supercritical N f n := by
  rw [cross_eq_prime_pair_sum]
  unfold lowPairs supercritical globalPairs
  apply (Finset.sum_product' n.primeFactors (n+1).primeFactors (coefficient N f)).symm.trans
  simpa only [not_le] using (sum_filter_add_sum_filter_not
    (n.primeFactors.product (n+1).primeFactors) (fun z => z.1*z.2 ≤ N)
    (fun z => coefficient N f z.1 z.2)).symm

lemma sum_supercritical_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ range N, supercritical N f n) =
      (∑ n ∈ range N, cross N f n) - subcritical N (coefficient N f) := by
  have he : (∑ n ∈ range N, cross N f n) =
      subcritical N (coefficient N f) + ∑ n ∈ range N, supercritical N f n := by
    simp_rw [cross_split]
    rw [sum_add_distrib, sum_lowPairs N _ (coefficient_swap N f)]
  rw [he]
  ring

/-- The actual supercritical prime-divisor-pair sum has mean zero, uniformly
for a different bounded prime function at each cutoff. -/
theorem supercritical_mean_tendsto_zero (f : ℕ → ℕ → ℝ) (hf : ∀ N p, |f N p| ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, supercritical N (f N) n)/N) atTop (𝓝 0) := by
  simp_rw [sum_supercritical_eq, sub_div]
  simpa using (cross_mean_tendsto_zero f hf).sub (subcritical_mean_tendsto_zero f hf)


noncomputable def magnitude (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ z ∈ globalPairs N n, |coefficient N f z.1 z.2|

lemma magnitude_nonneg (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : 0 ≤ magnitude N f n :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- For an increasing prime function, every remaining term has the direction
of the original largest-prime comparison, but a varying nonnegative size. -/
lemma supercritical_eq_signed_magnitude {N : ℕ} (hN : 1 < N) (f : ℕ → ℝ)
    (hf : Monotone f) {n : ℕ} (hn : n < N) :
    supercritical N f n = (Erdos371PrimeDiscrepancy.sign n : ℝ) * magnitude N f n := by
  unfold supercritical magnitude
  rw [mul_sum]
  apply sum_congr rfl
  rintro ⟨p,q⟩ hpq
  have hpql := hpq
  rw [global_eq_local_filter hn] at hpql
  have hs := Erdos371SupercriticalPrimePairs.pair_orientation (mem_filter.mp hpql).1
  have hl : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by exact_mod_cast hN)).le
  have hw : 0 ≤ (Real.log (p : ℝ)/Real.log N)*(Real.log (q : ℝ)/Real.log N) :=
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) hl)
      (div_nonneg (Real.log_natCast_nonneg q) hl)
  by_cases hlt : p < q
  · have hc : 0 ≤ coefficient N f p q := mul_nonneg hw (sub_nonneg.mpr (hf hlt.le))
    have hs' : Erdos371PrimeDiscrepancy.sign n = 1 := by simpa [hlt] using hs.symm
    simp [hs', abs_of_nonneg hc]
  · have hc : coefficient N f p q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw
      (sub_nonpos.mpr (hf (Nat.le_of_not_gt hlt)))
    have hs' : Erdos371PrimeDiscrepancy.sign n = -1 := by simpa [hlt] using hs.symm
    simp [hs', abs_of_nonpos hc]

/-- A genuine weighted signed-comparison theorem. No assertion that
`magnitude` tends to one is made. -/
theorem signed_magnitude_mean_tendsto_zero (f : ℕ → ℕ → ℝ)
    (hf : ∀ N p, |f N p| ≤ 1) (hm : ∀ N, Monotone (f N)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      (Erdos371PrimeDiscrepancy.sign n : ℝ)*magnitude N (f N) n)/N) atTop (𝓝 0) := by
  apply (supercritical_mean_tendsto_zero f hf).congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  congr 1
  apply sum_congr rfl
  intro n hn
  exact supercritical_eq_signed_magnitude hN (f N) (hm N) (mem_range.mp hn)

/-- The weights can vanish even at nontrivial strict largest-prime comparisons. -/
lemma magnitude_vanishes_example (f : ℕ → ℝ) :
    magnitude 55 f 44 = 0 ∧ Erdos371PrimeDiscrepancy.sign 44 = -1 := by
  have he : globalPairs 55 44 = ∅ := by decide +kernel
  constructor
  · simp [magnitude, he]
  · decide +kernel

end Erdos371WeightedSupercriticalCancellation

#print axioms Erdos371WeightedSupercriticalCancellation.supercritical_mean_tendsto_zero

#print axioms Erdos371WeightedSupercriticalCancellation.signed_magnitude_mean_tendsto_zero
