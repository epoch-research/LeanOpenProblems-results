import FormalConjecturesUtil
import Submission.SubcriticalPrimePairCancellation

/-! Reindexing the raw comparison by the actual prime-divisor sets, when
all prime-divisor products fit below the cutoff. A finite arithmetic example
shows that this raw comparison can vanish even in the pointwise low-product
region while the largest-prime comparison is a descent. This does not
disprove the density conjecture. -/

namespace Erdos371LowProductRawMismatch

open Finset Erdos371SubcriticalPrimePairCancellation

lemma prime_pair_filter {a b N : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hprod : Nat.maxPrimeFac a * Nat.maxPrimeFac b ≤ N) :
    ((pairs N).filter fun z => z.1 ∣ a ∧ z.2 ∣ b) =
      ((a.primeFactors.product b.primeFactors).filter fun z => z.1 < z.2) := by
  ext ⟨p,q⟩
  simp only [Finset.mem_filter, mem_pairs]
  constructor
  · rintro ⟨⟨hp,hq,hlt,_⟩,hpa,hqb⟩
    exact ⟨Finset.mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hpa,ha⟩,
      Nat.mem_primeFactors.mpr ⟨hq,hqb,hb⟩⟩,hlt⟩
  · rintro ⟨hpq,hlt⟩
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨hp,hpa,_⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨hq,hqb,_⟩ := Nat.mem_primeFactors.mp hq
    have hple := Nat.le_maxPrimeFac ha hp hpa
    have hqle := Nat.le_maxPrimeFac hb hq hqb
    exact ⟨⟨hp,hq,hlt,(Nat.mul_le_mul hple hqle).trans hprod⟩,hpa,hqb⟩

lemma localComparison_eq_counts (N n : ℕ) :
    localComparison N n =
      (((pairs N).filter fun z => z.1 ∣ n ∧ z.2 ∣ n+1).card : ℤ) -
      (((pairs N).filter fun z => z.2 ∣ n ∧ z.1 ∣ n+1).card : ℤ) := by
  simp [localComparison, Finset.sum_sub_distrib]

/-- The raw statistic counts every prime-divisor pair, even when the largest
pair fits below the cutoff. It is not reduced to a single comparison. -/
lemma localComparison_eq_factor_counts {n N : ℕ} (hn : n ≠ 0)
    (hprod : Nat.maxPrimeFac n * Nat.maxPrimeFac (n+1) ≤ N) :
    localComparison N n =
      (((n.primeFactors.product (n+1).primeFactors).filter fun z => z.1 < z.2).card : ℤ) -
      ((((n+1).primeFactors.product n.primeFactors).filter fun z => z.1 < z.2).card : ℤ) := by
  have hnext : n+1 ≠ 0 := by omega
  have hrev : Nat.maxPrimeFac (n+1) * Nat.maxPrimeFac n ≤ N := by
    simpa [Nat.mul_comm] using hprod
  rw [localComparison_eq_counts, prime_pair_filter hn hnext hprod]
  have he : ((pairs N).filter fun z => z.2 ∣ n ∧ z.1 ∣ n+1) =
      ((pairs N).filter fun z => z.1 ∣ n+1 ∧ z.2 ∣ n) := by
    ext z
    simp only [Finset.mem_filter, and_comm]
  rw [he, prime_pair_filter hnext hn hrev]

lemma prime_factors_example :
    (1376 : ℕ).primeFactors = {2,43} ∧
      (1377 : ℕ).primeFactors = {3,17} := by
  decide +kernel

lemma largest_factors_example :
    Nat.maxPrimeFac 1376 = 43 ∧ Nat.maxPrimeFac 1377 = 17 := by
  decide +kernel

lemma low_product_example :
    Nat.maxPrimeFac 1376 * Nat.maxPrimeFac 1377 ≤ 1377 := by
  rw [largest_factors_example.1, largest_factors_example.2]
  norm_num

lemma raw_zero_example : localComparison 1377 1376 = 0 := by
  rw [localComparison_eq_factor_counts (by norm_num) low_product_example]
  rw [prime_factors_example.1, prime_factors_example.2]
  decide +kernel

lemma descent_example : Erdos371PrimeDiscrepancy.sign 1376 = -1 := by
  decide +kernel

/-- An actual arithmetic mismatch, with product cutoff exactly `n+1`.
This is not a counterexample to any asymptotic density assertion. -/
theorem raw_can_vanish_in_pointwise_low_product_region :
    ∃ n : ℕ, 1 < n ∧
      Nat.maxPrimeFac n * Nat.maxPrimeFac (n+1) ≤ n+1 ∧
      localComparison (n+1) n = 0 ∧ Erdos371PrimeDiscrepancy.sign n = -1 := by
  exact ⟨1376, by norm_num, low_product_example, raw_zero_example, descent_example⟩

end Erdos371LowProductRawMismatch

#print axioms Erdos371LowProductRawMismatch.localComparison_eq_factor_counts
#print axioms Erdos371LowProductRawMismatch.raw_can_vanish_in_pointwise_low_product_region
