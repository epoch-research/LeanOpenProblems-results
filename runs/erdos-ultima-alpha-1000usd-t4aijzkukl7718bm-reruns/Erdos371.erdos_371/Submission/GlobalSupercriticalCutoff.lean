import FormalConjecturesUtil
import Submission.LocalSubcriticalCancellation
import Submission.SupercriticalPrimePairs

/-! Exact signed cancellation and an exact unsigned count for replacing the
local supercritical cutoff by the global counting-range cutoff. These facts
do not assert cancellation of the remaining supercritical score. -/

namespace Erdos371GlobalSupercriticalCutoff

open Finset Filter Erdos371PrimeDiscrepancy Erdos371CofactorSieve
open Erdos371LocalSubcriticalCancellation Erdos371ReflectionRange
open scoped Topology

abbrev localPairs := Erdos371SupercriticalPrimePairs.pairs
abbrev localMultiplicity := Erdos371SupercriticalPrimePairs.multiplicity
abbrev localSigned := Erdos371SupercriticalPrimePairs.signedPairs
abbrev smallPairs := Erdos371SubcriticalPrimePairCancellation.pairs

/-- Both orders of each pair of distinct primes with product at most `N`. -/
def orderedPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  smallPairs N ∪ (smallPairs N).image Prod.swap

lemma ordered_disjoint (N : ℕ) :
    Disjoint (smallPairs N) ((smallPairs N).image Prod.swap) := by
  apply disjoint_left.mpr
  rintro ⟨p,q⟩ hz hw
  have hpq := (Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz).2.2.1
  obtain ⟨⟨a,b⟩, hab, he⟩ := mem_image.mp hw
  have hab' := (Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hab).2.2.1
  have hp : b=p := congrArg Prod.fst he
  have hq : a=q := congrArg Prod.snd he
  omega

lemma mem_orderedPairs {N p q : ℕ} : (p,q) ∈ orderedPairs N ↔
    p.Prime ∧ q.Prime ∧ p ≠ q ∧ p*q ≤ N := by
  constructor
  · intro hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨hp,hq,hpq,hN⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
      exact ⟨hp,hq,hpq.ne,hN⟩
    · obtain ⟨⟨a,b⟩, hab, he⟩ := mem_image.mp hz
      have hp : b=p := congrArg Prod.fst he
      have hq : a=q := congrArg Prod.snd he
      obtain ⟨ha,hb,hab,hN⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hab
      subst p q
      exact ⟨hb,ha,hab.ne',by simpa [Nat.mul_comm] using hN⟩
  · rintro ⟨hp,hq,hpq,hN⟩
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact mem_union_left _ (Erdos371SubcriticalPrimePairCancellation.mem_pairs.mpr
        ⟨hp,hq,hlt,hN⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨(q,p),
        Erdos371SubcriticalPrimePairCancellation.mem_pairs.mpr
          ⟨hq,hp,hgt,by simpa [Nat.mul_comm] using hN⟩,rfl⟩)

lemma orderedPairs_card (N : ℕ) : (orderedPairs N).card = 2*(smallPairs N).card := by
  rw [orderedPairs,card_union_of_disjoint (ordered_disjoint N),
    card_image_of_injective _ Prod.swap_injective]
  omega

def globalPairs (N n : ℕ) : Finset (ℕ × ℕ) :=
  (n.primeFactors.product (n+1).primeFactors).filter fun z => N < z.1*z.2

def globalMultiplicity (N n : ℕ) : ℕ := (globalPairs N n).card

def globalSigned (N n : ℕ) : ℤ :=
  ∑ z ∈ globalPairs N n, if z.1 < z.2 then 1 else -1

def removedPairs (N n : ℕ) : Finset (ℕ × ℕ) :=
  (localPairs n).filter fun z => z.1*z.2 ≤ N

lemma removedPairs_eq (N n : ℕ) :
    removedPairs N n = (orderedPairs N).filter
      (fun z => z.1 ∣ n ∧ z.2 ∣ n+1 ∧ n+1 < z.1*z.2) := by
  ext ⟨p,q⟩
  constructor
  · intro hz
    obtain ⟨hz,hN⟩ := mem_filter.mp hz
    obtain ⟨hz,hprod⟩ := mem_filter.mp hz
    obtain ⟨hp,hq⟩ := mem_product.mp hz
    obtain ⟨hpprime,hpn,hn0⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨hqprime,hqn,_⟩ := Nat.mem_primeFactors.mp hq
    have hpq : p ≠ q := by
      intro he
      subst q
      have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hqn hpn
      exact hpprime.not_dvd_one h1
    exact mem_filter.mpr ⟨mem_orderedPairs.mpr ⟨hpprime,hqprime,hpq,hN⟩,
      hpn,hqn,hprod⟩
  · intro hz
    obtain ⟨hz,hpn,hqn,hprod⟩ := mem_filter.mp hz
    obtain ⟨hp,hq,hpq,hN⟩ := mem_orderedPairs.mp hz
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      exact hq.not_dvd_one (by simpa using hqn)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp,hpn,hn0⟩,
       Nat.mem_primeFactors.mpr ⟨hq,hqn,by omega⟩⟩,hprod⟩,hN⟩

lemma global_eq_local_filter {N n : ℕ} (hn : n < N) :
    globalPairs N n = (localPairs n).filter (fun z => ¬ z.1*z.2 ≤ N) := by
  ext z
  simp only [globalPairs,Erdos371SupercriticalPrimePairs.pairs,
    mem_filter,not_le]
  constructor
  · rintro ⟨hz,hprod⟩
    exact ⟨⟨hz,by omega⟩,hprod⟩
  · rintro ⟨⟨hz,_⟩,hprod⟩
    exact ⟨hz,hprod⟩

lemma multiplicity_split {N n : ℕ} (hn : n < N) :
    localMultiplicity n = (removedPairs N n).card + globalMultiplicity N n := by
  rw [globalMultiplicity,global_eq_local_filter hn]
  exact (card_filter_add_card_filter_not (s := localPairs n)
    (fun z => z.1*z.2 ≤ N)).symm

lemma globalMultiplicity_le {N n : ℕ} (hn : n < N) :
    globalMultiplicity N n ≤ localMultiplicity n := by
  rw [multiplicity_split hn]
  omega

/-- Each ordered prime pair contributes exactly one first-period root. -/
theorem removed_count_exact (N : ℕ) :
    (∑ n ∈ range N, (removedPairs N n).card) = 2*(smallPairs N).card := by
  simp only [removedPairs_eq,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ z ∈ orderedPairs N, (1:ℕ) := by
      apply sum_congr rfl
      rintro ⟨p,q⟩ hz
      obtain ⟨hp,hq,hpq,hN⟩ := mem_orderedPairs.mp hz
      rw [sum_boole]
      exact initial_count_one hp.one_lt hq.pos ((Nat.coprime_primes hp hq).mpr hpq) hN
    _ = _ := by simp [orderedPairs_card]

/-- The unsigned difference has an exact sparse-semiprime formula. -/
theorem multiplicity_difference_exact (N : ℕ) :
    (∑ n ∈ range N, ((localMultiplicity n : ℝ) - globalMultiplicity N n)) =
      2*(smallPairs N).card := by
  calc
    _ = ∑ n ∈ range N, ((removedPairs N n).card : ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [multiplicity_split (mem_range.mp hn),Nat.cast_add]
      ring
    _ = _ := by exact_mod_cast removed_count_exact N

lemma localSigned_split {N n : ℕ} (hn : n < N) :
    localSigned n = (∑ z ∈ removedPairs N n, if z.1 < z.2 then (1:ℤ) else -1) +
      globalSigned N n := by
  rw [globalSigned,global_eq_local_filter hn]
  exact (sum_filter_add_sum_filter_not (localPairs n) (fun z => z.1*z.2 ≤ N)
    (fun z => if z.1 < z.2 then (1:ℤ) else -1)).symm

lemma removed_signed_sum (N : ℕ) :
    (∑ n ∈ range N, ∑ z ∈ removedPairs N n,
      if z.1 < z.2 then (1:ℤ) else -1) = 0 := by
  simp only [removedPairs_eq,sum_filter]
  rw [sum_comm]
  have he : (∑ z ∈ orderedPairs N, ∑ n ∈ range N,
      if z.1 ∣ n ∧ z.2 ∣ n+1 ∧ n+1 < z.1*z.2
      then (if z.1 < z.2 then (1:ℤ) else -1) else 0) =
      ∑ z ∈ orderedPairs N, if z.1 < z.2 then (1:ℤ) else -1 := by
    apply sum_congr rfl
    rintro ⟨p,q⟩ hz
    obtain ⟨hp,hq,hpq,hN⟩ := mem_orderedPairs.mp hz
    rw [← sum_filter,sum_const,initial_count_one hp.one_lt hq.pos
      ((Nat.coprime_primes hp hq).mpr hpq) hN]
    simp
  rw [he,orderedPairs,sum_union (ordered_disjoint N),sum_image Prod.swap_injective.injOn]
  rw [← sum_add_distrib]
  apply sum_eq_zero
  rintro ⟨p,q⟩ hz
  have hpq := (Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz).2.2.1
  simp [hpq,not_lt_of_ge hpq.le]

/-- The two signed supercritical sums are exactly equal, even though the
multiplicities may differ at individual inputs. -/
theorem signed_sum_exact (N : ℕ) :
    (∑ n ∈ range N, localSigned n) = ∑ n ∈ range N, globalSigned N n := by
  calc
    _ = (∑ n ∈ range N, ∑ z ∈ removedPairs N n,
        if z.1 < z.2 then (1:ℤ) else -1) + ∑ n ∈ range N, globalSigned N n := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun n hn => localSigned_split (mem_range.mp hn))
    _ = _ := by rw [removed_signed_sum,zero_add]

lemma globalSigned_eq {N n : ℕ} (hn : n < N) :
    globalSigned N n = (globalMultiplicity N n : ℤ) * sign n := by
  unfold globalSigned
  have hh : ∀ z ∈ globalPairs N n,
      (if z.1 < z.2 then (1:ℤ) else -1) = sign n := by
    intro z hz
    rw [global_eq_local_filter hn] at hz
    exact Erdos371SupercriticalPrimePairs.pair_orientation (mem_filter.mp hz).1
  rw [sum_congr rfl hh]
  simp [globalMultiplicity]

/-- Changing the supercritical cutoff is harmless in mean absolute error. -/
theorem multiplicity_error_mean_zero :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, |(localMultiplicity n : ℝ) - globalMultiplicity N n|)/N)
      atTop (𝓝 0) := by
  have he (N : ℕ) : (∑ n ∈ range N,
      |(localMultiplicity n : ℝ) - globalMultiplicity N n|) = 2*(smallPairs N).card := by
    rw [← multiplicity_difference_exact N]
    apply sum_congr rfl
    intro n hn
    exact abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr
      (globalMultiplicity_le (mem_range.mp hn))))
  simp only [he]
  have hu := semiCount_ratio_zero.const_mul 2
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    positivity
  · intro N
    have hc : ((smallPairs N).card : ℝ) ≤ semiCount N := Nat.cast_le.mpr
      (Erdos371SubcriticalPrimePairCancellation.pairs_card_le N)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 2)) (Nat.cast_nonneg (α := ℝ) N)

lemma globalMultiplicity_pos_iff {n : ℕ} (hn : 1 < n) (N : ℕ) :
    0 < globalMultiplicity N n ↔ N < P n * P (n+1) := by
  rw [globalMultiplicity,card_pos]
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

/-- The number of inputs where even one pair is changed is sparse. -/
lemma changed_inputs_bound (N : ℕ) :
    ((range N).filter fun n => localMultiplicity n ≠ globalMultiplicity N n).card ≤
      2*(smallPairs N).card := by
  rw [← removed_count_exact N,card_eq_sum_ones,sum_filter]
  apply sum_le_sum
  intro n hn
  have hs := multiplicity_split (mem_range.mp hn)
  split_ifs <;> omega

theorem changed_inputs_mean_zero :
    Tendsto (fun N : ℕ =>
      (((range N).filter fun n => localMultiplicity n ≠ globalMultiplicity N n).card : ℝ)/N)
      atTop (𝓝 0) := by
  have hu := semiCount_ratio_zero.const_mul 2
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    positivity
  · intro N
    have hc : (((range N).filter fun n =>
        localMultiplicity n ≠ globalMultiplicity N n).card : ℝ) ≤ 2*semiCount N := by
      exact_mod_cast (changed_inputs_bound N).trans
        (Nat.mul_le_mul_left 2 (Erdos371SubcriticalPrimePairCancellation.pairs_card_le N))
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc
      (Nat.cast_nonneg (α := ℝ) N)

end Erdos371GlobalSupercriticalCutoff

#print axioms Erdos371GlobalSupercriticalCutoff.removed_count_exact
#print axioms Erdos371GlobalSupercriticalCutoff.signed_sum_exact
#print axioms Erdos371GlobalSupercriticalCutoff.multiplicity_error_mean_zero

#print axioms Erdos371GlobalSupercriticalCutoff.changed_inputs_mean_zero
