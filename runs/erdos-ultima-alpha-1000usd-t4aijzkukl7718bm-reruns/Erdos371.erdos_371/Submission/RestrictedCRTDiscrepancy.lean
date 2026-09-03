import FormalConjecturesUtil
import Submission.LargeDivisorSignedEnergy
import Submission.SupercriticalPrimePairs

/-! In the supercritical range, the largest-prime restriction on a
prime-divisor subgroup is automatic. Its signed sum is precisely a difference
of two CRT progression counts. This does not estimate their aggregate. -/

namespace Erdos371RestrictedCRTDiscrepancy

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371LargeDivisorSignedEnergy
open Erdos371SubcriticalPrimePairCancellation (count)

lemma up_eq_progression {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hprod : N < p*q) :
    up p q N = (range N).filter (fun n => q ∣ n ∧ p ∣ n+1) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have he : P (n+1)=p := by simpa [winner,max_eq_right hcmp.le] using hwin
    exact mem_filter.mpr ⟨hnN,by simpa [lower,hcmp] using hdiv,
      he ▸ Nat.maxPrimeFac_dvd⟩
  · intro hn
    obtain ⟨hnN,hqn,hpn⟩ := mem_filter.mp hn
    have hn0 : 0 < n := by
      by_contra h
      have he : n=0 := by omega
      subst n
      exact hp.not_dvd_one (by simpa using hpn)
    have ho := Erdos371SupercriticalPrimePairs.orientation hn0 hq hp hqn hpn
      (by have := mem_range.mp hnN; simpa [Nat.mul_comm] using (show n+1 < p*q by omega))
    have hwin : winner n=p := by simpa [max_eq_right hqp.le] using ho.1.symm
    have hcmp := ho.2.mp hqp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hnN,hwin,by simpa [lower,hcmp] using hqn⟩,hcmp⟩

lemma down_eq_progression {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hprod : N < p*q) :
    down p q N = (range N).filter (fun n => p ∣ n ∧ q ∣ n+1) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have he : P n=p := by simpa [winner,max_eq_left (le_of_not_gt hcmp)] using hwin
    exact mem_filter.mpr ⟨hnN,he ▸ Nat.maxPrimeFac_dvd,by simpa [lower,hcmp] using hdiv⟩
  · intro hn
    obtain ⟨hnN,hpn,hqn⟩ := mem_filter.mp hn
    have hn0 : 0 < n := by
      by_contra h
      have he : n=0 := by omega
      subst n
      exact hq.not_dvd_one (by simpa using hqn)
    have ho := Erdos371SupercriticalPrimePairs.orientation hn0 hp hq hpn hqn
      (by have := mem_range.mp hnN; omega)
    have hwin : winner n=p := by simpa [max_eq_left hqp.le] using ho.1.symm
    have hcmp : ¬P n<P (n+1) := by intro h; have := ho.2.mpr h; omega
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hnN,hwin,by simpa [lower,hcmp] using hqn⟩,hcmp⟩

/-- Removing the largest-prime restriction is valid here because `p*q>N`.
The remaining first-moment sum over prime pairs is not estimated. -/
theorem restrictedGroup_eq_crt_difference {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hprod : N < p*q) :
    restrictedGroup p q N = (count q p N : ℝ)-count p q N := by
  rw [restrictedGroup_eq_counts,up_eq_progression hp hq hqp hprod,
    down_eq_progression hp hq hqp hprod]
  rfl

/-- Below the product cutoff the restriction cannot simply be removed. -/
lemma small_product_restriction_matters :
    5*2 ≤ 20 ∧ restrictedGroup 5 2 20 = -1 ∧ count 2 5 20 = count 5 2 20 := by
  constructor
  · norm_num
  constructor
  · rw [restrictedGroup_eq_counts]
    have hu : (up 5 2 20).card=1 := by decide +kernel
    have hd : (down 5 2 20).card=2 := by decide +kernel
    rw [hu,hd]
    norm_num
  · decide +kernel

end Erdos371RestrictedCRTDiscrepancy

#print axioms Erdos371RestrictedCRTDiscrepancy.restrictedGroup_eq_crt_difference
#print axioms Erdos371RestrictedCRTDiscrepancy.small_product_restriction_matters
