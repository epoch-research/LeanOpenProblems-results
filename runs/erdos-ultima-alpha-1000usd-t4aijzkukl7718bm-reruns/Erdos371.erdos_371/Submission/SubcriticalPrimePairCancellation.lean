import FormalConjecturesUtil
import Submission.ReflectionRange
import Submission.CofactorSieve

/-! Unconditional cancellation for unweighted prime-divisor pairs below the
counting-range product cutoff. This is NOT largest-prime-factor cancellation. -/

namespace Erdos371SubcriticalPrimePairCancellation

open Finset Filter Erdos371ReflectionRange Erdos371CofactorSieve
open scoped Topology

def count (a b N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => a ∣ n ∧ b ∣ n+1).card

lemma count_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (N : ℕ) :
    |(count a b N : ℝ) - (N : ℝ)/(a*b : ℕ)| ≤ 1 := by
  obtain ⟨v,hv,hav,hbv⟩ := exists_progression_origin ha hb hab
  have hp (n : ℕ) : (a ∣ n+a*b ∧ b ∣ n+a*b+1) ↔ (a ∣ n ∧ b ∣ n+1) := by
    have hd₁ : a ∣ a*b := dvd_mul_right a b
    have hd₂ : b ∣ a*b := dvd_mul_left b a
    have he : n+a*b+1 = (n+1)+a*b := by omega
    rw [he, ← Nat.dvd_add_iff_left hd₁, ← Nat.dvd_add_iff_left hd₂]
  have hsingle : (Finset.range (a*b)).filter (fun n => a ∣ n ∧ b ∣ n+1) = {v} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn,han,hbn⟩
      have he := progression_remainder hab hv hav hbv han hbn
      simpa [Nat.mod_eq_of_lt hn] using he
    · rintro rfl
      exact ⟨hv,hav,hbv⟩
  have h := Erdos371ResidueSieve.periodic_count_error
    (fun n => a ∣ n ∧ b ∣ n+1) (Nat.mul_pos ha hb) hp N
  simpa only [hsingle, Finset.card_singleton, Nat.cast_one, mul_one, count] using h

lemma reversed_count_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (N : ℕ) :
    |(count a b N : ℝ) - count b a N| ≤ 2 := by
  have h₁ := count_error ha hb hab N
  have h₂ := count_error hb ha hab.symm N
  rw [Nat.mul_comm b a] at h₂
  calc
    _ ≤ |(count a b N : ℝ) - (N : ℝ)/(a*b : ℕ)| +
        |(N : ℝ)/(a*b : ℕ) - count b a N| := abs_sub_le _ _ _
    _ ≤ 2 := by rw [abs_sub_comm ((N : ℝ)/(a*b : ℕ))]; linarith

def pairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (((N+1).primesBelow).product ((N+1).primesBelow)).filter
    fun z => z.1 < z.2 ∧ z.1*z.2 ≤ N

lemma mem_pairs {N p q : ℕ} : (p,q) ∈ pairs N ↔
    p.Prime ∧ q.Prime ∧ p < q ∧ p*q ≤ N := by
  change ((p,q) ∈ (((N+1).primesBelow).product ((N+1).primesBelow)).filter
    (fun z => z.1 < z.2 ∧ z.1*z.2 ≤ N)) ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hm,hlt,hprod⟩
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hm
    exact ⟨(Nat.mem_primesBelow.mp hp).2,(Nat.mem_primesBelow.mp hq).2,hlt,hprod⟩
  · rintro ⟨hp,hq,hlt,hprod⟩
    have hple : p ≤ p*q := Nat.le_mul_of_pos_right p hq.pos
    have hqle : q ≤ p*q := Nat.le_mul_of_pos_left q hp.pos
    exact ⟨Finset.mem_product.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,
      Nat.mem_primesBelow.mpr ⟨by omega,hq⟩⟩,hlt,hprod⟩

lemma pairs_card_le (N : ℕ) : (pairs N).card ≤ semiCount N := by
  classical
  unfold semiCount
  apply Finset.card_le_card_of_injOn (fun z : ℕ × ℕ => z.1*z.2-1)
  · rintro ⟨p,q⟩ hz
    obtain ⟨hp,hq,hlt,hprod⟩ := mem_pairs.mp hz
    have hpos := Nat.mul_pos hp.pos hq.pos
    change p*q-1 ∈ (Finset.range N).filter (fun n => semiprime (n+1))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      ⟨p,q,hp,hq,by omega⟩⟩
  · rintro ⟨p,q⟩ hz ⟨r,s⟩ hw he
    obtain ⟨hp,hq,hpq,hprod⟩ := mem_pairs.mp hz
    obtain ⟨hr,hs,hrs,hprod'⟩ := mem_pairs.mp hw
    have hpos := Nat.mul_pos hp.pos hq.pos
    have hpos' := Nat.mul_pos hr.pos hs.pos
    have hprod_eq : p*q = r*s := by
      change p*q-1 = r*s-1 at he
      omega
    obtain ⟨rfl,rfl⟩ := prime_factors_determined_by_product_and_order
      hp hq hr hs hprod_eq (by simp [hpq,hrs])
    rfl

noncomputable def discrepancy (N : ℕ) : ℝ :=
  ∑ z ∈ pairs N, ((count z.1 z.2 N : ℝ) - count z.2 z.1 N)

lemma discrepancy_bound (N : ℕ) : |discrepancy N| ≤ 2 * semiCount N := by
  calc
    _ ≤ ∑ z ∈ pairs N, |(count z.1 z.2 N : ℝ) - count z.2 z.1 N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ pairs N, (2 : ℝ) := by
      apply Finset.sum_le_sum
      rintro ⟨p,q⟩ hz
      obtain ⟨hp,hq,hpq,_⟩ := mem_pairs.mp hz
      exact reversed_count_error hp.pos hq.pos
        ((Nat.coprime_primes hp hq).mpr (Nat.ne_of_lt hpq)) N
    _ ≤ 2 * semiCount N := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have h : ((pairs N).card : ℝ) ≤ semiCount N := Nat.cast_le.mpr (pairs_card_le N)
      linarith

/-- A genuine signed arithmetic estimate, but for ALL prime-divisor pairs,
not just the largest prime divisors of the two consecutive integers. -/
theorem discrepancy_mean_tendsto_zero :
    Tendsto (fun N : ℕ => discrepancy N / N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hu : Tendsto (fun N : ℕ => 2 * ((semiCount N : ℝ)/N)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul semiCount_ratio_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    exact abs_nonneg _
  · intro N
    change |discrepancy N / (N : ℝ)| ≤ 2 * ((semiCount N : ℝ)/N)
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (discrepancy_bound N) (Nat.cast_nonneg (α := ℝ) N)

/-- This counts every prime-divisor pair meeting the product cutoff. -/
def localComparison (N n : ℕ) : ℤ :=
  ∑ z ∈ pairs N,
    ((if z.1 ∣ n ∧ z.2 ∣ n+1 then 1 else 0) -
      (if z.2 ∣ n ∧ z.1 ∣ n+1 then 1 else 0))

lemma discrepancy_eq_local_sum (N : ℕ) :
    discrepancy N = ∑ n ∈ Finset.range N, (localComparison N n : ℝ) := by
  unfold discrepancy localComparison
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp [count, Finset.sum_sub_distrib]

/-- Even when ALL prime-divisor pairs fit below the product cutoff,
`localComparison` need not agree with the largest-prime-factor sign. -/
lemma local_comparison_not_largest_comparison :
    localComparison 55 44 = 0 ∧
    Erdos371PrimeDiscrepancy.sign 44 = -1 ∧
    Nat.maxPrimeFac 44 * Nat.maxPrimeFac 45 ≤ 55 := by
  decide +kernel

end Erdos371SubcriticalPrimePairCancellation

#print axioms Erdos371SubcriticalPrimePairCancellation.discrepancy_mean_tendsto_zero

#print axioms Erdos371SubcriticalPrimePairCancellation.local_comparison_not_largest_comparison
