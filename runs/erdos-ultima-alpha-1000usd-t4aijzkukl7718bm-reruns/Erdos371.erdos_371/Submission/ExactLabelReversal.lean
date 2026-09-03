import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! A necessary range condition for reversing both largest-prime labels.
It does not obstruct arbitrary sign-reversing matchings and proves no density
claim about the two orientations. -/

namespace Erdos371ExactLabelReversal

open Erdos371PrimeDiscrepancy

lemma neighboring_labels_coprime {n : ℕ} (hn : 1 < n) :
    (P n).Coprime (P (n+1)) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  exact (Nat.coprime_primes hp hq).mpr (Ne.symm (consecutive_ne n))

/-- Reversing both labels forces a congruence modulo their product. -/
theorem reverse_product_dvd {n m : ℕ} (hn : 1 < n)
    (hl : P n = P (m+1)) (hr : P (n+1) = P m) :
    P n * P (n+1) ∣ n+m+1 := by
  have hqm : P n ∣ m+1 := hl ▸ Nat.maxPrimeFac_dvd
  have hpm : P (n+1) ∣ m := hr ▸ Nat.maxPrimeFac_dvd
  apply (neighboring_labels_coprime hn).mul_dvd_of_dvd_of_dvd
  · simpa only [Nat.add_assoc] using Nat.dvd_add (Nat.maxPrimeFac_dvd (n := n)) hqm
  · have hh := Nat.dvd_add (Nat.maxPrimeFac_dvd (n := n+1)) hpm
    convert hh using 1
    omega

lemma reverse_product_le {n m : ℕ} (hn : 1 < n)
    (hl : P n = P (m+1)) (hr : P (n+1) = P m) :
    P n * P (n+1) ≤ n+m+1 :=
  Nat.le_of_dvd (by omega) (reverse_product_dvd hn hl hr)

/-- A large prime-label product prevents a reversal in a fixed linear range.
This concerns preservation of the labels, not merely reversal of their order. -/
theorem no_linear_label_reversal {n N C : ℕ} (hn : 1 < n) (hnN : n < N)
    (hprod : (C+1)*N < P n * P (n+1)) :
    ¬ ∃ m ≤ C*N, P n = P (m+1) ∧ P (n+1) = P m := by
  rintro ⟨m, hm, hl, hr⟩
  have hh := reverse_product_le hn hl hr
  nlinarith

/-- Keeping both labels in their original order forces the input difference
to be divisible by their product. -/
theorem same_order_product_dvd_sub {n m : ℕ} (hn : 1 < n)
    (hl : P n = P m) (hr : P (n+1) = P (m+1)) :
    P n * P (n+1) ∣ m-n := by
  have hqm : P n ∣ m := hl ▸ Nat.maxPrimeFac_dvd
  have hpm : P (n+1) ∣ m+1 := hr ▸ Nat.maxPrimeFac_dvd
  apply (neighboring_labels_coprime hn).mul_dvd_of_dvd_of_dvd
  · exact Nat.dvd_sub hqm Nat.maxPrimeFac_dvd
  · simpa using Nat.dvd_sub hpm (Nat.maxPrimeFac_dvd (n := n+1))

/-- A pair of labels with product at least the cutoff identifies at most one
input in that range. -/
theorem same_order_unique_in_range {n m N : ℕ} (hn : 1 < n) (hnm : n ≤ m)
    (hmN : m < N) (hprod : N ≤ P n * P (n+1))
    (hl : P n = P m) (hr : P (n+1) = P (m+1)) : n=m := by
  by_contra h
  have hd := same_order_product_dvd_sub hn hl hr
  have hh := Nat.le_of_dvd (by omega : 0 < m-n) hd
  omega

end Erdos371ExactLabelReversal

#print axioms Erdos371ExactLabelReversal.reverse_product_dvd
#print axioms Erdos371ExactLabelReversal.no_linear_label_reversal
#print axioms Erdos371ExactLabelReversal.same_order_unique_in_range
