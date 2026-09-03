import FormalConjecturesUtil
import Submission.CRTReflectedRoot

/-! The exact correction to removing the largest-prime restriction from a
CRT progression count. The correction is a SIGNED count of inputs possessing
a still larger prime; no asymptotic cancellation of it is asserted. -/

namespace Erdos371CRTRestrictionError

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371LargeDivisorSignedEnergy
open Erdos371SubcriticalPrimePairCancellation (count)

lemma up_eq_bounded_progression {N p q : ℕ} (hp : p.Prime) :
    up p q N = (range N).filter
      (fun n => q ∣ n ∧ p ∣ n+1 ∧ winner n ≤ p) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have he : P (n+1)=p := by simpa [winner,max_eq_right hcmp.le] using hwin
    exact mem_filter.mpr ⟨hnN,by simpa [lower,hcmp] using hdiv,
      he ▸ Nat.maxPrimeFac_dvd,hwin.le⟩
  · intro hn
    obtain ⟨hnN,hqn,hpn,hwin⟩ := mem_filter.mp hn
    have hpP : p ≤ P (n+1) := Nat.le_maxPrimeFac (by omega) hp hpn
    have hP : P n ≤ p ∧ P (n+1) ≤ p := max_le_iff.mp hwin
    have hcmp : P n<P (n+1) := by have := consecutive_ne n; omega
    have hw : winner n=p := by unfold winner; omega
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hnN,hw,by simpa [lower,hcmp] using hqn⟩,hcmp⟩

lemma down_eq_bounded_progression {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    down p q N = (range N).filter
      (fun n => p ∣ n ∧ q ∣ n+1 ∧ winner n ≤ p) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have he : P n=p := by simpa [winner,max_eq_left (le_of_not_gt hcmp)] using hwin
    exact mem_filter.mpr ⟨hnN,he ▸ Nat.maxPrimeFac_dvd,
      by simpa [lower,hcmp] using hdiv,hwin.le⟩
  · intro hn
    obtain ⟨hnN,hpn,hqn,hwin⟩ := mem_filter.mp hn
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      exact hq.not_dvd_one (by simpa using hqn)
    have hpP : p ≤ P n := Nat.le_maxPrimeFac hn0 hp hpn
    have hP : P n ≤ p ∧ P (n+1) ≤ p := max_le_iff.mp hwin
    have hcmp : ¬P n<P (n+1) := by omega
    have hw : winner n=p := by unfold winner; omega
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hnN,hw,by simpa [lower,hcmp] using hqn⟩,hcmp⟩

def excessUp (p q N : ℕ) : ℕ :=
  ((range N).filter (fun n => q ∣ n ∧ p ∣ n+1 ∧ p<winner n)).card

def excessDown (p q N : ℕ) : ℕ :=
  ((range N).filter (fun n => p ∣ n ∧ q ∣ n+1 ∧ p<winner n)).card

noncomputable def correction (p q N : ℕ) : ℝ :=
  (excessUp p q N : ℝ)-excessDown p q N

lemma up_count_split {p : ℕ} (hp : p.Prime) (q N : ℕ) :
    count q p N = (up p q N).card+excessUp p q N := by
  have hh := card_filter_add_card_filter_not
    (s := (range N).filter (fun n => q ∣ n ∧ p ∣ n+1)) (fun n => winner n ≤ p)
  have hu : ((range N).filter (fun n => q ∣ n ∧ p ∣ n+1)).filter
      (fun n => winner n ≤ p) = up p q N := by
    rw [up_eq_bounded_progression hp]
    ext n
    simp only [mem_filter,and_assoc]
  have hd : ((range N).filter (fun n => q ∣ n ∧ p ∣ n+1)).filter
      (fun n => ¬winner n ≤ p) =
        (range N).filter (fun n => q ∣ n ∧ p ∣ n+1 ∧ p<winner n) := by
    ext n
    simp only [mem_filter,not_le,and_assoc]
  rw [hu,hd] at hh
  exact hh.symm

lemma down_count_split {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (N : ℕ) :
    count p q N = (down p q N).card+excessDown p q N := by
  have hh := card_filter_add_card_filter_not
    (s := (range N).filter (fun n => p ∣ n ∧ q ∣ n+1)) (fun n => winner n ≤ p)
  have hu : ((range N).filter (fun n => p ∣ n ∧ q ∣ n+1)).filter
      (fun n => winner n ≤ p) = down p q N := by
    rw [down_eq_bounded_progression hp hq]
    ext n
    simp only [mem_filter,and_assoc]
  have hd : ((range N).filter (fun n => p ∣ n ∧ q ∣ n+1)).filter
      (fun n => ¬winner n ≤ p) =
        (range N).filter (fun n => p ∣ n ∧ q ∣ n+1 ∧ p<winner n) := by
    ext n
    simp only [mem_filter,not_le,and_assoc]
  rw [hu,hd] at hh
  exact hh.symm

/-- The CRT estimate controls `restrictedGroup + correction`, not either
summand separately. -/
theorem group_add_correction {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (N : ℕ) :
    restrictedGroup p q N+correction p q N = (count q p N : ℝ)-count p q N := by
  rw [restrictedGroup_eq_counts,up_count_split hp q N,down_count_split hp hq N]
  unfold correction
  push_cast
  ring

lemma group_add_correction_abs_le_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q<p) (N : ℕ) : |restrictedGroup p q N+correction p q N| ≤ 1 := by
  rw [group_add_correction hp hq]
  exact Erdos371CRTReflectedRoot.difference_abs_le_one hq.pos hp.pos
    ((Nat.coprime_primes hq hp).mpr hqp.ne) N

/-- Every excluded occurrence has a third, strictly larger prime. One of
its products with the two prescribed divisors must fit inside the range. -/
theorem excluded_has_third_prime {p q N n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q<p) (hn : n<N) (hpn : p ∣ n) (hqn : q ∣ n+1) (hwin : p<winner n) :
    ∃ r : ℕ, r.Prime ∧ p<r ∧ (r ∣ n ∨ r ∣ n+1) ∧ (p*r ≤ N ∨ q*r ≤ N) := by
  have hn0 : 0<n := by
    by_contra hh
    have he : n=0 := by omega
    subst n
    exact hq.not_dvd_one (by simpa using hqn)
  refine ⟨winner n,winner_prime hn0,hwin,?_⟩
  by_cases hh : P n ≤ P (n+1)
  · have he : winner n=P (n+1) := max_eq_right hh
    have hd : winner n ∣ n+1 := he ▸ Nat.maxPrimeFac_dvd
    refine ⟨Or.inr hd,Or.inr ?_⟩
    have hb := Erdos371SupercriticalPrimePairs.distinct_prime_product_le
      (by omega : 0<n+1) hq (winner_prime hn0) (by omega : q ≠ winner n) hqn hd
    omega
  · have he : winner n=P n := max_eq_left (Nat.le_of_not_ge hh)
    have hd : winner n ∣ n := he ▸ Nat.maxPrimeFac_dvd
    refine ⟨Or.inl hd,Or.inl ?_⟩
    have hb := Erdos371SupercriticalPrimePairs.distinct_prime_product_le
      hn0 hp (winner_prime hn0) hwin.ne hpn hd
    omega

lemma correction_nonzero_example : correction 5 2 20=1 := by
  have hh := group_add_correction (p := 5) (q := 2) (by norm_num) (by norm_num) 20
  rw [Erdos371RestrictedCRTDiscrepancy.small_product_restriction_matters.2.1,
    Erdos371RestrictedCRTDiscrepancy.small_product_restriction_matters.2.2,sub_self] at hh
  linarith

end Erdos371CRTRestrictionError

#print axioms Erdos371CRTRestrictionError.group_add_correction
#print axioms Erdos371CRTRestrictionError.group_add_correction_abs_le_one
#print axioms Erdos371CRTRestrictionError.excluded_has_third_prime
#print axioms Erdos371CRTRestrictionError.correction_nonzero_example
