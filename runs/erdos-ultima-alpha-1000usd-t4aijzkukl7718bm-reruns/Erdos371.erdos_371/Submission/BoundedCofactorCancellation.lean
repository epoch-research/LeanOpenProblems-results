import FormalConjecturesUtil
import Submission.SieveLogDecay
import Submission.CofactorDiscrepancy
import Submission.ElementaryEnergy

/-! Cancellation in winning-prime groups along fixed bounded cofactor ranges.
These estimates do not cover the growing cofactors needed in Erdős 371. -/

namespace Erdos371BoundedCofactorCancellation

open Finset Filter Erdos371PrimeDiscrepancy Erdos371CofactorDiscrepancy
open Erdos371CofactorSieve Erdos371SieveParameters Erdos371SieveLogDecay
open scoped Topology

attribute [local instance] Classical.propDecidable

def regular (A p : ℕ) : Prop := ∀ a ∈ Finset.Icc 1 A,
  P (a*p-1) < p ∧ P (a*p+1) < p

lemma prime_multiple_small {A a p : ℕ} (hp : p.Prime) (hAp : A < p)
    (ha : a ∈ Finset.Icc 1 A) : P (a*p) = p := by
  obtain ⟨ha1,haA⟩ := Finset.mem_Icc.mp ha
  rw [P,Nat.maxPrimeFac_mul (by omega) hp.ne_zero,hp.maxPrimeFac_eq_self,
    max_eq_right (Nat.maxPrimeFac_le.trans (by omega : a ≤ p))]

lemma regular_group {A p : ℕ} (hA : 0 < A) (hp : p.Prime) (hAp : A < p)
    (hr : regular A p) : group p (A*p) = 1 := by
  have hminus : ((Finset.Icc 1 A).filter
      (fun a => P a ≤ p ∧ P (a*p-1) < p)) = Finset.Icc 1 A := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    exact ⟨Nat.maxPrimeFac_le.trans (by have := (Finset.mem_Icc.mp ha).2; omega), (hr a ha).1⟩
  have hplus : ((Finset.Icc 1 A).filter
      (fun a => P a ≤ p ∧ P (a*p+1) < p)) = Finset.Icc 1 A := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    exact ⟨Nat.maxPrimeFac_le.trans (by have := (Finset.mem_Icc.mp ha).2; omega), (hr a ha).2⟩
  have hAmem : A ∈ Finset.Icc 1 A := Finset.mem_Icc.mpr ⟨hA,le_rfl⟩
  rw [group_eq_cofactorDifference hp,cofactorDifference,Nat.mul_div_cancel _ hp.pos,
    hminus,hplus,sub_self,zero_add]
  simp [prime_multiple_small hp hAp hAmem,(hr A hAmem).2]

lemma bounded_cofactor_of_large_prime {A p t : ℕ} (hp : 2 ≤ p)
    (hlt : p ≤ P t) (ht : t ≤ A*p+1) :
    ∃ b ∈ Finset.Icc 1 A, b ∣ t ∧ (t/b).Prime ∧ p ≤ t/b := by
  have hPt : P t ≤ t := Nat.maxPrimeFac_le
  have ht1 : 1 < t := by omega
  have hq : (P t).Prime := Nat.prime_maxPrimeFac_of_one_lt t ht1
  let b := t/P t
  have hbpos : 0 < b := Nat.div_pos hPt hq.pos
  have he : b*P t = t := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  have hbA : b ≤ A := by
    by_contra h
    have hm := Nat.mul_le_mul (show A+1 ≤ b by omega) hlt
    nlinarith
  have hbt : b ∣ t := ⟨P t,he.symm⟩
  have hquot : t/b = P t := by
    calc
      t/b = (b*P t)/b := congrArg (fun x => x/b) he.symm
      _ = P t := Nat.mul_div_right _ hbpos
  exact ⟨b,Finset.mem_Icc.mpr ⟨hbpos,hbA⟩,hbt,hquot ▸ hq,hquot ▸ hlt⟩

lemma irregular_in_box_image {A p k N : ℕ} (hp : p.Prime) (hAp : A < p)
    (hpN : p < N) (hcut : cutoff k ≤ p) (hbad : ¬regular A p) :
    p ∈ (cofactorBox k 1 A (A*N+1)).image (fun n => min (P n) (P (n+1))) := by
  simp only [regular,not_forall] at hbad
  obtain ⟨a,ha⟩ := hbad
  obtain ⟨hamem,hbad⟩ := ha
  obtain ⟨ha1,haA⟩ := Finset.mem_Icc.mp hamem
  have hapos : 0 < a*p := Nat.mul_pos ha1 hp.pos
  have hapN : a*p ≤ A*N := Nat.mul_le_mul haA hpN.le
  have hPap := prime_multiple_small hp hAp hamem
  have hdiv : a ∣ a*p := dvd_mul_right a p
  have hquot : (a*p)/a = p := Nat.mul_div_right p ha1
  rcases not_and_or.mp hbad with hminus | hplus
  · have hge : p ≤ P (a*p-1) := Nat.le_of_not_gt hminus
    obtain ⟨b,hb,hbd,hbprime,hbge⟩ := bounded_cofactor_of_large_prime hp.two_le hge
      (show a*p-1 ≤ A*p+1 by have := Nat.mul_le_mul_right p haA; omega)
    have he : a*p-1+1 = a*p := by omega
    apply Finset.mem_image.mpr
    refine ⟨a*p-1,?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨b,hb,Finset.mem_biUnion.mpr ⟨a,hamem,?_⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),hbd,?_,hbprime,?_,hcut.trans hbge,?_⟩
      · simpa only [he] using hdiv
      · simpa only [he,hquot] using hp
      · simpa only [he,hquot] using hcut
    · rw [he,hPap,min_eq_right hge]
  · have hge : p ≤ P (a*p+1) := Nat.le_of_not_gt hplus
    obtain ⟨b,hb,hbd,hbprime,hbge⟩ := bounded_cofactor_of_large_prime hp.two_le hge
      (show a*p+1 ≤ A*p+1 by nlinarith [Nat.mul_le_mul_right p haA])
    apply Finset.mem_image.mpr
    refine ⟨a*p,?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨a,hamem,Finset.mem_biUnion.mpr ⟨b,hb,?_⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),hdiv,hbd,?_,hbprime,?_,hcut.trans hbge⟩
      · simpa only [hquot] using hp
      · simpa only [hquot] using hcut
    · rw [hPap,min_eq_left hge]

noncomputable def irregularPrimes (A N : ℕ) : Finset ℕ :=
  N.primesBelow.filter fun p => p ≤ A ∨ ¬regular A p

lemma irregularPrimes_card_bound (A k N : ℕ) :
    (irregularPrimes A N).card ≤ A+cutoff k+1+(cofactorBox k 1 A (A*N+1)).card := by
  have hsub : irregularPrimes A N ⊆ Finset.range (A+cutoff k+1) ∪
      (cofactorBox k 1 A (A*N+1)).image (fun n => min (P n) (P (n+1))) := by
    intro p hp
    obtain ⟨hpN,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hp⟩ := Nat.mem_primesBelow.mp hpN
    by_cases hsmall : p < A+cutoff k+1
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hsmall)
    · apply Finset.mem_union_right
      apply irregular_in_box_image hp (by omega) hpN (by omega)
      exact hbad.resolve_left (by omega)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    simpa only [Finset.card_range] using Nat.add_le_add_left
      (Finset.card_image_le (s := cofactorBox k 1 A (A*N+1))
        (f := fun n => min (P n) (P (n+1)))) (A+cutoff k+1)))

lemma irregularPrimes_sieve_bound {A : ℕ} (hA : 0 < A) (k N : ℕ)
    (hN : 0 < N) (hlarge : threshold k ≤ N) :
    ((irregularPrimes A N).card : ℝ) ≤
      ((A:ℝ)+1+6*(Real.exp 1)^2*(A+2)*A^2)*
        (1+(cutoff k:ℝ)+(N:ℝ)/(4:ℝ)^k) := by
  have hT : threshold k ≤ A*N+2 := by nlinarith
  have hs := cofactorBox_card_bound (by norm_num : 0 < (1:ℕ)) k A
    (A*N+1) (A*N+2) (by simp) hT
  have hcount := Nat.cast_le (α := ℝ).mpr (irregularPrimes_card_bound A k N)
  push_cast at hs hcount
  have hAN : (A:ℝ)*N+2 ≤ ((A:ℝ)+2)*N := by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hden : 0 ≤ (N:ℝ)/(4:ℝ)^k := by positivity
  have hc : 0 ≤ (cutoff k:ℝ) := by positivity
  have hconst : 0 ≤ 6*(Real.exp 1)^2*((A:ℝ)+2)*A^2 := by positivity
  have hs' : ((cofactorBox k 1 A (A*N+1)).card : ℝ) ≤
      (6*(Real.exp 1)^2*((A:ℝ)+2)*A^2)*((N:ℝ)/(4:ℝ)^k) := by
    calc
      _ ≤ 6*(Real.exp 1)^2*((A:ℝ)*N+2)*A^2/(4:ℝ)^k := hs
      _ ≤ 6*(Real.exp 1)^2*(((A:ℝ)+2)*N)*A^2/(4:ℝ)^k := by gcongr
      _ = _ := by ring
  nlinarith [Nat.cast_nonneg (α := ℝ) A]

/-- For each fixed cofactor bound, only `o(X/log X)` primes below `X`
are too small or have an irregular neighbor among the first `A` multiples. -/
theorem irregularPrimes_log_ratio_tendsto_zero {A : ℕ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => ((irregularPrimes A N).card : ℝ)*Real.log N/N)
      atTop (𝓝 0) := by
  apply log_decay_of_sieve_bound
    (C := (A:ℝ)+1+6*(Real.exp 1)^2*(A+2)*A^2)
    (fun _ => Nat.cast_nonneg _) (by positivity)
  exact fun k N hN hlarge => irregularPrimes_sieve_bound hA k N hN hlarge

noncomputable def deviation (A N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, |(group p (A*p) : ℝ)-1|

lemma deviation_nonneg (A N : ℕ) : 0 ≤ deviation A N :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma deviation_bound {A : ℕ} (hA : 0 < A) (N : ℕ) :
    deviation A N ≤ (A+1:ℝ)*(irregularPrimes A N).card := by
  have he : deviation A N = ∑ p ∈ irregularPrimes A N, |(group p (A*p) : ℝ)-1| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hg : ¬(p ≤ A ∨ ¬regular A p) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hp,h⟩)
    have hAp : A < p := Nat.lt_of_not_ge (not_or.mp hg).1
    have hr : regular A p := not_not.mp (not_or.mp hg).2
    simp [regular_group hA hp' hAp hr]
  rw [he]
  calc
    _ ≤ ∑ _p ∈ irregularPrimes A N, (A+1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
      have hbound := Erdos371ElementaryEnergy.group_abs_le_div hp' (A*p)
      rw [Nat.mul_div_cancel _ hp'.pos] at hbound
      exact (abs_sub _ _).trans (by norm_num; linarith)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Absolute group deviations from the boundary term have logarithmic decay
for each fixed `A`. The counting endpoint of each group here is `A*p`. -/
theorem deviation_log_ratio_tendsto_zero {A : ℕ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => deviation A N*Real.log N/N) atTop (𝓝 0) := by
  have hu := (irregularPrimes_log_ratio_tendsto_zero hA).const_mul (A+1:ℝ)
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    exact div_nonneg (mul_nonneg (deviation_nonneg A N) (Real.log_natCast_nonneg N))
      (Nat.cast_nonneg N)
  · intro N
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (deviation_bound hA N) (Real.log_natCast_nonneg N))
      (Nat.cast_nonneg (α := ℝ) N)
    simpa only [mul_assoc,mul_div_assoc] using hh


end Erdos371BoundedCofactorCancellation

#print axioms Erdos371BoundedCofactorCancellation.regular_group
#print axioms Erdos371BoundedCofactorCancellation.irregularPrimes_log_ratio_tendsto_zero
#print axioms Erdos371BoundedCofactorCancellation.deviation_log_ratio_tendsto_zero
