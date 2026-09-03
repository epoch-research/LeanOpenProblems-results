import Submission.FirstHitTransfer
import Submission.FirstHitMainSum
import Submission.SieveReferenceCriterion

/-! Prior divisor supports on a common index type, with their exact prime
normalizers and cutoff-squared coefficient budgets. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]

noncomputable def priorDivisorSupport (p : ι → ℕ) (i : ι) (R : ℕ) : Finset (Finset ι) :=
  (divisorSupport p R).filter (fun T => T ⊆ Iio i)

lemma mem_priorDivisorSupport (p : ι → ℕ) (i : ι) (R : ℕ) (T : Finset ι) :
    T ∈ priorDivisorSupport p i R ↔ (∏ j ∈ T, p j) ≤ R ∧ T ⊆ Iio i := by
  simp only [priorDivisorSupport, mem_filter, mem_divisorSupport]

lemma priorDivisorSupport_nonempty (p : ι → ℕ) (i : ι) (R : ℕ) (hR : 0 < R) :
    (priorDivisorSupport p i R).Nonempty := by
  refine ⟨∅, (mem_priorDivisorSupport p i R ∅).mpr ?_⟩
  simpa using And.intro hR (empty_subset (Iio i))

lemma priorDivisorSupport_downward (p : ι → ℕ) (hp : ∀ j, 1 ≤ p j) (i : ι) (R : ℕ)
    (A : Finset ι) (hA : A ∈ priorDivisorSupport p i R) (B : Finset ι) (hBA : B ⊆ A) :
    B ∈ priorDivisorSupport p i R := by
  obtain ⟨hAR, hAi⟩ := mem_filter.mp hA
  exact mem_filter.mpr ⟨divisorSupport_downward p hp R A hAR B hBA, hBA.trans hAi⟩

lemma priorDivisorSupport_prior (p : ι → ℕ) (i : ι) (R : ℕ)
    (T : Finset ι) (hT : T ∈ priorDivisorSupport p i R) (j : ι) (hj : j ∈ T) : j < i :=
  mem_Iio.mp (((mem_priorDivisorSupport p i R T).mp hT).2 hj)

lemma priorDivisorSupport_card_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (i : ι) (R : ℕ) : (priorDivisorSupport p i R).card ≤ R :=
  (card_le_card (filter_subset _ _)).trans (divisorSupport_card_le p hp hpinj R)

lemma normalizer_priorDivisorSupport (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (i : ι) (R : ℕ) :
    normalizer (fun j => 1 / (p j : ℝ)) (priorDivisorSupport p i R) =
      primeNormalizer ((Iio i).image p) R := by
  rw [normalizer_eq_prime_sum p hp]
  apply sum_bij (fun T _ => T.image p)
  · intro T hT
    obtain ⟨hTR, hTi⟩ := (mem_priorDivisorSupport p i R T).mp hT
    apply (mem_smallDivisorFamily _ _ _).mpr
    refine ⟨image_subset_image hTi, ?_⟩
    rwa [prod_image hpinj.injOn]
  · intro A hA B hB hAB
    exact image_injective hpinj hAB
  · intro Q hQ
    obtain ⟨hQi, hQR⟩ := (mem_smallDivisorFamily _ _ _).mp hQ
    obtain ⟨T, hTi, heq⟩ := subset_image_iff.mp hQi
    refine ⟨T, (mem_priorDivisorSupport p i R T).mpr ⟨?_, hTi⟩, heq⟩
    rwa [← heq, prod_image hpinj.injOn] at hQR
  · intro T hT
    exact (prod_image (f := fun a : ℕ => 1 / ((a : ℝ) - 1)) hpinj.injOn).symm

noncomputable def firstPrimeList (k : ℕ) (i : Fin k) : ℕ := Nat.nth Nat.Prime i.val

lemma firstPrimeList_prime (k : ℕ) (i : Fin k) : (firstPrimeList k i).Prime := Nat.prime_nth_prime i.val

lemma firstPrimeList_strictMono (k : ℕ) : StrictMono (firstPrimeList k) :=
  fun _ _ hij => Nat.nth_strictMono Nat.infinite_setOf_prime hij

lemma firstPrimeList_prior_image (k : ℕ) (i : Fin k) :
    (Iio i).image (firstPrimeList k) = (firstPrimeList k i).primesBelow := by
  ext q
  constructor
  · intro hq
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
    exact Nat.mem_primesBelow.mpr ⟨firstPrimeList_strictMono k (mem_Iio.mp hj), firstPrimeList_prime k j⟩
  · intro hq
    obtain ⟨hqi, hqprime⟩ := Nat.mem_primesBelow.mp hq
    let j := Nat.count Nat.Prime q
    have heq : Nat.nth Nat.Prime j = q := Nat.nth_count hqprime
    have hjlt : j < i.val := by
      by_contra hn
      have hh := Nat.nth_monotone Nat.infinite_setOf_prime (show i.val ≤ j by omega)
      rw [heq] at hh
      exact (not_le_of_gt hqi) hh
    refine mem_image.mpr ⟨⟨j, hjlt.trans i.isLt⟩, mem_Iio.mpr hjlt, heq⟩

lemma primeNormalizer_ge_one (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : 0 < N) :
    1 ≤ primeNormalizer P N := by
  have hempty : ∅ ∈ smallDivisorFamily P N := by
    apply (mem_smallDivisorFamily _ _ _).mpr
    simpa using And.intro (empty_subset P) hN
  have hh := single_le_sum (s := smallDivisorFamily P N) (f := primeWeight)
    (fun Q hQ => primeWeight_nonneg Q (fun p hp => hP p (((mem_smallDivisorFamily _ _ _).mp hQ).1 hp))) hempty
  simpa only [primeWeight, prod_empty] using hh

lemma reference_prior_normalizer (k : ℕ) (i : Fin k) (N : ℕ) :
    normalizer (fun j => 1 / (firstPrimeList k j : ℝ)) (priorDivisorSupport (firstPrimeList k) i N) =
      primeNormalizer (firstPrimeList k i).primesBelow N := by
  rw [normalizer_priorDivisorSupport _ (firstPrimeList_prime k) (firstPrimeList_strictMono k).injective,
    firstPrimeList_prior_image]

lemma reference_prior_main_le (k : ℕ) (L : ℝ)
    (hbound : ∀ i : Fin k, firstPrimeList k i ≤ firstHitPrimeCut L 0) :
    (∑ i : Fin k, (1 / (firstPrimeList k i : ℝ)) /
      normalizer (fun j => 1 / (firstPrimeList k j : ℝ))
        (priorDivisorSupport (firstPrimeList k) i (firstHitCutoff L (firstPrimeList k i)))) ≤ firstHitMainSum L := by
  simp_rw [reference_prior_normalizer]
  have hsub : univ.image (firstPrimeList k) ⊆ (firstHitPrimeCut L 0 + 1).primesBelow := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨firstPrimeList_prime k i, hbound i⟩
  rw [← sum_image (f := fun p : ℕ => (1 / (p : ℝ)) /
    primeNormalizer p.primesBelow (firstHitCutoff L p)) (s := univ)
    (firstPrimeList_strictMono k).injective.injOn]
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro p hp hn
  have hpp := (WeightedMertens.mem_primes.mp hp).1
  have hG := primeNormalizer_ge_one p.primesBelow (firstHitCutoff L p)
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) (firstHitCutoff_pos L p)
  positivity

#print axioms normalizer_priorDivisorSupport
#print axioms reference_prior_main_le
end Erdos970.FiniteSelberg
