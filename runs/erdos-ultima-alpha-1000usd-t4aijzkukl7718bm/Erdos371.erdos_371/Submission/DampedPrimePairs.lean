import Submission.DampedComparison

/-! Large cross-prime products in the quadratic damping term. Their signed
sum retains an input-dependent multiplicity; no cancellation is asserted. -/
namespace Erdos371
open Finset

private lemma distinct_prime_product_dvd {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpm : p ∣ m) (hqm : q ∣ m) : p*q ∣ m := by
  apply (hp.coprime_iff_not_dvd.mpr ?_).mul_dvd_of_dvd_of_dvd hpm hqm
  intro h
  exact hpq ((hq.dvd_iff_eq hp.ne_one).mp h).symm

lemma cross_prime_pair_max_bound (n p q r : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : p ∣ n) (hqn : q ∣ n+1) (hrn : r ∣ n*(n+1))
    (hsize : n+1 < p*q) : r ≤ max p q := by
  by_contra h
  have hpr : p < r := (le_max_left p q).trans_lt (lt_of_not_ge h)
  have hqr : q < r := (le_max_right p q).trans_lt (lt_of_not_ge h)
  rcases hr.dvd_mul.mp hrn with hrn | hrn
  · have hd := distinct_prime_product_dvd hp hr (ne_of_lt hpr) hpn hrn
    have hb := Nat.le_of_dvd hn hd
    have hm := Nat.mul_le_mul_left p hqr.le
    omega
  · have hd := distinct_prime_product_dvd hq hr (ne_of_lt hqr) hqn hrn
    have hb := Nat.le_of_dvd (show 0 < n+1 by omega) hd
    have hm := Nat.mul_le_mul_left q hpr.le
    nlinarith

/-- Any cross-prime pair whose product exceeds the interval endpoint
contains the global largest prime factor. -/
theorem large_cross_prime_pair_max (N n p q : ℕ) (hn : 0 < n) (hnN : n+1 ≤ N)
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n+1)
    (hpq : N < p*q) : Nat.maxPrimeFac (n*(n+1)) = max p q := by
  have hm : 1 < n*(n+1) := by nlinarith
  apply le_antisymm
  · exact cross_prime_pair_max_bound n p q _ hn hp hq
      (Nat.prime_maxPrimeFac_of_one_lt _ hm) hpn hqn Nat.maxPrimeFac_dvd
      (hnN.trans_lt hpq)
  · apply max_le
    · exact Nat.le_maxPrimeFac (by positivity) hp (dvd_mul_of_dvd_left hpn _)
    · exact Nat.le_maxPrimeFac (by positivity) hq (dvd_mul_of_dvd_right hqn _)

lemma large_cross_prime_pair_order (N n p q : ℕ) (hn : 1 < n) (hnN : n+1 ≤ N)
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n+1)
    (hpq : N < p*q) : (p < q ↔ Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) := by
  have hpne : p ≠ q := by
    intro he
    subst q
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpn).mpr hqn)
  have hsize : n+1 < p*q := hnN.trans_lt hpq
  have hrise (h : p < q) : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by
    have hpnmax : Nat.maxPrimeFac n < q := by
      by_contra hbad
      have hqmax := le_of_not_gt hbad
      have hpmax : p ≠ Nat.maxPrimeFac n := ne_of_lt (h.trans_le hqmax)
      have hd := distinct_prime_product_dvd hp
        (Nat.prime_maxPrimeFac_of_one_lt n hn) hpmax hpn Nat.maxPrimeFac_dvd
      have hb := Nat.le_of_dvd (by omega : 0 < n) hd
      have hh := Nat.mul_le_mul_left p hqmax
      omega
    exact hpnmax.trans_le (Nat.le_maxPrimeFac (by omega) hq hqn)
  refine ⟨hrise,?_⟩
  intro h
  by_contra hbad
  have hqp : q < p := lt_of_le_of_ne (le_of_not_gt hbad) (Ne.symm hpne)
  have hqmax : Nat.maxPrimeFac (n+1) < p := by
    by_contra hbad
    have hpmax := le_of_not_gt hbad
    have hqmax : q ≠ Nat.maxPrimeFac (n+1) := ne_of_lt (hqp.trans_le hpmax)
    have hd := distinct_prime_product_dvd hq
      (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)) hqmax hqn Nat.maxPrimeFac_dvd
    have hb := Nat.le_of_dvd (by omega : 0 < n+1) hd
    have hh := Nat.mul_le_mul_left q hpmax
    nlinarith
  have hpmax := Nat.le_maxPrimeFac (by omega : n ≠ 0) hp hpn
  omega

def largeCrossPrimePairs (N n : ℕ) : Finset (ℕ×ℕ) :=
  (n.primeFactors ×ˢ (n+1).primeFactors).filter fun pq => N < pq.1*pq.2

noncomputable def largeCrossPrimePairSkew (N n : ℕ) : ℝ :=
  ∑ pq ∈ largeCrossPrimePairs N n, if pq.1 < pq.2 then 1 else -1

/-- The quadratic large-product contribution is the actual comparison sign
multiplied by a variable number of cross-prime pairs. -/
theorem largeCrossPrimePairSkew_eq (N n : ℕ) (hn : 1 < n) (hnN : n+1 ≤ N) :
    largeCrossPrimePairSkew N n = (largeCrossPrimePairs N n).card * factorSign n := by
  unfold largeCrossPrimePairSkew
  have he (pq : ℕ×ℕ) (hpq : pq ∈ largeCrossPrimePairs N n) :
      (if pq.1 < pq.2 then (1 : ℝ) else -1) = factorSign n := by
    obtain ⟨hpq,hsize⟩ := mem_filter.mp hpq
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    simp only [factorSign,predicateSign,large_cross_prime_pair_order N n pq.1 pq.2 hn hnN
      (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq) hsize]
  rw [sum_congr rfl he,sum_const,nsmul_eq_mul]

lemma largeCrossPrimePairSkew_eq_of_pos (N n : ℕ) (hn : 0 < n) (hnN : n+1 ≤ N) :
    largeCrossPrimePairSkew N n = (largeCrossPrimePairs N n).card * factorSign n := by
  by_cases hn1 : 1 < n
  · exact largeCrossPrimePairSkew_eq N n hn1 hnN
  · have he : n=1 := by omega
    subst n
    simp [largeCrossPrimePairSkew,largeCrossPrimePairs]

/-- The residual weight can be zero or nonzero on rising comparisons;
it cannot be removed from the signed identity as a constant. -/
lemma largeCrossPrimePairs_variable_weight :
    (largeCrossPrimePairs 30 8).card=0 ∧ (largeCrossPrimePairs 30 20).card=1 := by
  decide +kernel

#print axioms large_cross_prime_pair_max
#print axioms largeCrossPrimePairSkew_eq
end Erdos371
