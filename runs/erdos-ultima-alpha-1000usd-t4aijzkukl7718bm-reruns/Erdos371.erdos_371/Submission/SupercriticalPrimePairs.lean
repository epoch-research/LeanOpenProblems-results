import FormalConjecturesUtil
import Submission.PrimeDiscrepancy
import Submission.UnboundedPrimeDeletionLocal

/-! Prime-divisor pairs above the input-size product cutoff all point in the
same direction as the largest-prime comparison. Their multiplicity need not
be one, and this file does not prove cancellation of their signed sum. -/

namespace Erdos371SupercriticalPrimePairs

open Finset Erdos371PrimeDiscrepancy

lemma distinct_prime_product_le {n p r : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hpn : p ∣ n) (hrn : r ∣ n) :
    p*r ≤ n := by
  have hcop : p.Coprime r := (Nat.coprime_primes hp hr).mpr hpr
  exact Nat.le_of_dvd hn (hcop.mul_dvd_of_dvd_of_dvd hpn hrn)

/-- In a pair above the size cutoff, the prime on the side with the larger
largest prime factor must itself be that largest prime factor. -/
lemma top_prime_on_larger_side {u v p q : ℕ} (hu : 1 < u) (hv : 0 < v)
    (hp : p.Prime) (hq : q.Prime) (hpu : p ∣ u) (hqv : q ∣ v)
    (horder : P v < P u) (hprod : max u v < p*q) :
    p = P u ∧ q < p := by
  have hqle : q ≤ P v := Nat.le_maxPrimeFac hv.ne' hq hqv
  have ht : (P u).Prime := Nat.prime_maxPrimeFac_of_one_lt u hu
  have he : p = P u := by
    by_contra hne
    have hb := distinct_prime_product_le (by omega : 0 < u) hp ht hne
      hpu (Nat.maxPrimeFac_dvd (n := u))
    have hmul := Nat.mul_le_mul_left p (hqle.trans horder.le)
    have huM : u ≤ max u v := le_max_left _ _
    omega
  exact ⟨he, he ▸ hqle.trans_lt horder⟩

/-- The arithmetic orientation of every supercritical prime-divisor pair. -/
theorem orientation {n p q : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n+1)
    (hprod : n+1 < p*q) :
    max p q = winner n ∧ (p < q ↔ P n < P (n+1)) := by
  have hn1 : 1 < n := hp.one_lt.trans_le (Nat.le_of_dvd hn hpn)
  have hne := consecutive_ne n
  rcases lt_or_gt_of_ne hne.symm with hup | hdown
  · have hh := top_prime_on_larger_side (u := n+1) (v := n)
      (by omega) hn hq hp hqn hpn hup (by simpa [max_eq_left (by omega : n ≤ n+1), Nat.mul_comm] using hprod)
    constructor
    · rw [max_eq_right hh.2.le, winner, max_eq_right hup.le, hh.1]
    · exact ⟨fun _ => hup, fun _ => hh.2⟩
  · have hh := top_prime_on_larger_side hn1 (by omega) hp hq hpn hqn hdown
      (by simpa [max_eq_right (by omega : n ≤ n+1)] using hprod)
    constructor
    · rw [max_eq_left hh.2.le, winner, max_eq_left hdown.le, hh.1]
    · exact ⟨fun h => False.elim (by omega), fun h => False.elim (by omega)⟩

def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.primeFactors.product (n+1).primeFactors).filter fun z => n+1 < z.1*z.2

def multiplicity (n : ℕ) : ℕ := (pairs n).card

def signedPairs (n : ℕ) : ℤ :=
  ∑ z ∈ pairs n, if z.1 < z.2 then 1 else -1

lemma pair_orientation {n : ℕ} {z : ℕ × ℕ} (hz : z ∈ pairs n) :
    (if z.1 < z.2 then (1:ℤ) else -1) = sign n := by
  obtain ⟨hmem,hprod⟩ := mem_filter.mp hz
  obtain ⟨hp,hq⟩ := mem_product.mp hmem
  have hn : 0 < n := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2
  have hh := (orientation hn (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hq) hprod).2
  simp only [hh, sign]

/-- A positive multiplicity, rather than an unweighted comparison, appears. -/
theorem signedPairs_eq (n : ℕ) : signedPairs n = (multiplicity n : ℤ) * sign n := by
  unfold signedPairs
  rw [sum_congr rfl (fun z hz => pair_orientation hz)]
  simp [multiplicity]

lemma multiplicity_pos_iff {n : ℕ} (hn : 1 < n) :
    0 < multiplicity n ↔ n+1 < P n * P (n+1) := by
  rw [multiplicity, card_pos]
  constructor
  · rintro ⟨⟨p,q⟩,hz⟩
    obtain ⟨hm,hprod⟩ := mem_filter.mp hz
    obtain ⟨hp,hq⟩ := mem_product.mp hm
    have hpl := Nat.le_maxPrimeFac (by omega : n ≠ 0)
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    have hql := Nat.le_maxPrimeFac (by omega : n+1 ≠ 0)
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
    exact hprod.trans_le (Nat.mul_le_mul hpl hql)
  · intro hprod
    refine ⟨(P n,P (n+1)),mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,hprod⟩⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn,
        Nat.maxPrimeFac_dvd,by omega⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),
        Nat.maxPrimeFac_dvd,by omega⟩

lemma pairs_before_prime {q : ℕ} (hq : q.Prime) :
    pairs (q-1) = (q-1).primeFactors.product {q} := by
  have he : q-1+1 = q := by have := hq.two_le; omega
  unfold pairs
  rw [he,hq.primeFactors]
  apply filter_eq_self.mpr
  intro z hz
  obtain ⟨hp,hzq⟩ := mem_product.mp hz
  have hqeq : z.2 = q := mem_singleton.mp hzq
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  rw [hqeq]
  nlinarith [hq.pos]

lemma multiplicity_before_prime {q : ℕ} (hq : q.Prime) :
    multiplicity (q-1) = (q-1).primeFactors.card := by
  simp [multiplicity,pairs_before_prime hq]

/-- Even in the supercritical region the multiplicity is unbounded. -/
theorem multiplicity_unbounded (K : ℕ) :
    ∃ n : ℕ, 1 < n ∧ K ≤ multiplicity n := by
  obtain ⟨q,hq,hq2,hK⟩ :=
    Erdos371UnboundedPrimeDeletionLocal.exists_prime_with_many_factors_predecessor K
  exact ⟨q-1,by omega,by simpa [multiplicity_before_prime hq] using hK⟩

end Erdos371SupercriticalPrimePairs

#print axioms Erdos371SupercriticalPrimePairs.orientation
#print axioms Erdos371SupercriticalPrimePairs.signedPairs_eq
#print axioms Erdos371SupercriticalPrimePairs.multiplicity_unbounded
