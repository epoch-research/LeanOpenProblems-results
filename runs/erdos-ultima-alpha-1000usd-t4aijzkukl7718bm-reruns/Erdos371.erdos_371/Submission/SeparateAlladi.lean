import FormalConjecturesUtil
import Submission.AlladiExplore
import Submission.PrimeDiscrepancy

/-! Separate inclusion–exclusion expansions for the two consecutive integers.
Their indexing divisors are at most the counting endpoint, not its square. -/

namespace Erdos371SeparateAlladi

open Erdos371Exploration Erdos371PrimeDiscrepancy

def below (k p : ℕ) : ℤ := if k < p then 1 else 0

lemma separate_expansion {n : ℕ} (hn : 1 < n) :
    sign n =
      (∑ t ∈ n.primeFactors.powerset, minWeight (below (P (n + 1))) t) -
      (∑ t ∈ (n + 1).primeFactors.powerset, minWeight (below (P n)) t) := by
  rw [alladi_primeFactors _ hn, alladi_primeFactors _ (by omega)]
  have hne := consecutive_ne n
  unfold sign below
  by_cases h : P n < P (n + 1)
  · simp [h, Nat.not_lt_of_ge h.le]
  · have hh : P (n + 1) < P n := by omega
    simp [h, hh]

lemma expansion_divisor_le {n : ℕ} (hn : 0 < n)
    {t : Finset ℕ} (ht : t ∈ n.primeFactors.powerset) :
    (∏ p ∈ t, p) ≤ n := by
  have hd : (∏ p ∈ t, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset t n.primeFactors id (Finset.mem_powerset.mp ht)).trans
      (Nat.prod_primeFactors_dvd n)
  exact Nat.le_of_dvd hn hd

def roughWeight (k d : ℕ) : ℤ :=
  if 1 < d ∧ k < d.minFac then ArithmeticFunction.moebius d else 0

lemma squarefree_prime_product {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq)
  · intro p hp
    exact (ht p hp).squarefree

lemma roughWeight_prime_product (k : ℕ) {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    roughWeight k (∏ p ∈ t, p) = minWeight (below k) t := by
  by_cases hne : t.Nonempty
  · have hs := squarefree_prime_product ht
    have hprod : 1 < ∏ p ∈ t, p := by
      have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos (fun p hp => (ht p hp).pos)
      exact (ht _ (t.min'_mem hne)).one_lt.trans_le
        (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem id (t.min'_mem hne)))
    have hm : (∏ p ∈ t, p).minFac = t.min' hne := by
      have hmem : (∏ p ∈ t, p).minFac ∈ t := by
        have hh : (∏ p ∈ t, p).minFac ∈ (∏ p ∈ t, p).primeFactors :=
          Nat.mem_primeFactors.mpr
            ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, hs.ne_zero⟩
        simpa only [Nat.primeFactors_prod ht] using hh
      exact le_antisymm
        (Nat.minFac_le_of_dvd (ht _ (t.min'_mem hne)).two_le
          (Finset.dvd_prod_of_mem id (t.min'_mem hne)))
        (t.min'_le _ hmem)
    have hc : ArithmeticFunction.cardFactors (∏ p ∈ t, p) = t.card := by
      rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
        hs.ne_zero).mpr hs, ArithmeticFunction.cardDistinctFactors_apply,
        ← List.card_toFinset, Nat.toFinset_factors, Nat.primeFactors_prod ht]
    have hmu : ArithmeticFunction.moebius (∏ p ∈ t, p) = (-1 : ℤ) ^ t.card := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hs, hc]
    unfold roughWeight minWeight below
    rw [dif_pos hne, hmu, hm]
    by_cases h : k < t.min' hne <;> simp [hprod, h]
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst t
    simp [roughWeight, minWeight]

lemma alladi_divisor_form {n : ℕ} (hn : 1 < n) (k : ℕ) :
    (∑ d ∈ n.divisors, roughWeight k d) = -below k (P n) := by
  have he : (∑ d ∈ n.divisors, roughWeight k d) =
      ∑ d ∈ n.divisors with Squarefree d, roughWeight k d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : Squarefree d
    · simp [hs]
    · simp [hs, roughWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  rw [he, Nat.sum_divisors_filter_squarefree (by omega : n ≠ 0), Nat.factors_eq]
  simp only [List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val]
  change (∑ t ∈ n.primeFactors.powerset, roughWeight k (∏ p ∈ t, p)) = _
  have hh : (∑ t ∈ n.primeFactors.powerset, roughWeight k (∏ p ∈ t, p)) =
      ∑ t ∈ n.primeFactors.powerset, minWeight (below k) t := by
    apply Finset.sum_congr rfl
    intro t ht
    apply roughWeight_prime_product
    intro p hp
    exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp ht) hp)).1
  rw [hh]
  exact alladi_primeFactors _ hn

lemma separate_divisor_expansion {n : ℕ} (hn : 1 < n) :
    sign n =
      (∑ d ∈ n.divisors, roughWeight (P (n + 1)) d) -
      (∑ d ∈ (n + 1).divisors, roughWeight (P n) d) := by
  rw [alladi_divisor_form hn, alladi_divisor_form (by omega : 1 < n + 1)]
  have hne := consecutive_ne n
  unfold sign below
  by_cases h : P n < P (n + 1)
  · simp [h, Nat.not_lt_of_ge h.le]
  · have hh : P (n + 1) < P n := by omega
    simp [h, hh]

end Erdos371SeparateAlladi

#print axioms Erdos371SeparateAlladi.separate_expansion
#print axioms Erdos371SeparateAlladi.expansion_divisor_le

#print axioms Erdos371SeparateAlladi.separate_divisor_expansion
