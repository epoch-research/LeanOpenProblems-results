import FormalConjecturesUtil
import Submission.GlobalSupercriticalCutoff

/-! A two-sided fixed multiplicative band around the critical product has
natural density zero. This is a size restriction, not orientation balance. -/

namespace Erdos371CriticalProductBand

open Finset Filter Erdos371PrimeDiscrepancy Erdos371CofactorSieve
open Erdos371GlobalSupercriticalCutoff Erdos371ReflectionRange
open scoped Topology

/-- The product of the largest primes is within a factor `C` of the input. -/
def critical (C n : ℕ) : Prop :=
  1 < n ∧ n ≤ C*(P n*P (n+1)) ∧ P n*P (n+1) ≤ C*n

instance (C n : ℕ) : Decidable (critical C n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def code (n : ℕ) : (ℕ × ℕ) × ℕ :=
  ((P n,P (n+1)),n/(P n*P (n+1)))

lemma code_injective {n m : ℕ} (hn : 1 < n)
    (he : code n = code m) : n=m := by
  have hpair := congrArg Prod.fst he
  have hp : P n=P m := congrArg Prod.fst hpair
  have hq : P (n+1)=P (m+1) := congrArg Prod.snd hpair
  have hk : n/(P n*P (n+1))=m/(P m*P (m+1)) := congrArg Prod.snd he
  rw [← hp,← hq] at hk
  have hpn := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hqn := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have hcop : (P n).Coprime (P (n+1)) :=
    (Nat.coprime_primes hpn hqn).mpr (consecutive_ne n).symm
  obtain ⟨v,hv,hpv,hqv⟩ := exists_progression_origin hpn.pos hqn.pos hcop
  have hrn := progression_remainder hcop hv hpv hqv
    (Nat.maxPrimeFac_dvd (n := n)) (Nat.maxPrimeFac_dvd (n := n+1))
  have hpm : P n ∣ m := hp ▸ Nat.maxPrimeFac_dvd
  have hqm : P (n+1) ∣ m+1 := hq ▸ Nat.maxPrimeFac_dvd
  have hrm := progression_remainder hcop hv hpv hqv hpm hqm
  have hn' := Nat.mod_add_div n (P n*P (n+1))
  have hm' := Nat.mod_add_div m (P n*P (n+1))
  rw [hrn,hk] at hn'
  rw [hrm] at hm'
  omega

lemma code_mem {C N n : ℕ} (hn : n < N) (hc : critical C n) :
    code n ∈ (orderedPairs (C*N)).product (range (C+1)) := by
  obtain ⟨hn1,hlo,hhi⟩ := hc
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn1
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  apply mem_product.mpr
  constructor
  · exact mem_orderedPairs.mpr ⟨hp,hq,(consecutive_ne n).symm,
      hhi.trans (Nat.mul_le_mul_left C hn.le)⟩
  · apply mem_range.mpr
    have hd := Nat.div_le_div_right (c := P n*P (n+1)) hlo
    rw [Nat.mul_div_cancel _ (Nat.mul_pos hp.pos hq.pos)] at hd
    exact Nat.lt_succ_of_le hd

/-- One ordered prime pair and one CRT-period index determine the input. -/
theorem critical_count_bound (C N : ℕ) :
    ((range N).filter (critical C)).card ≤ 2*(C+1)*semiCount (C*N) := by
  have hc : ((range N).filter (critical C)).card ≤
      ((orderedPairs (C*N)).product (range (C+1))).card := by
    apply card_le_card_of_injOn code
    · intro n hn
      change n ∈ (range N).filter (critical C) at hn
      obtain ⟨hn,hc⟩ := mem_filter.mp hn
      exact code_mem (mem_range.mp hn) hc
    · intro n hn m hm he
      change n ∈ (range N).filter (critical C) at hn
      exact code_injective (mem_filter.mp hn).2.1 he
  have he : ((orderedPairs (C*N)).product (range (C+1))).card =
      (orderedPairs (C*N)).card * (range (C+1)).card := Finset.card_product _ _
  rw [he,card_range,orderedPairs_card] at hc
  have hs := Erdos371SubcriticalPrimePairCancellation.pairs_card_le (C*N)
  nlinarith

/-- The critical band is negligible on BOTH sides of the product threshold. -/
theorem critical_hasDensity_zero (C : ℕ) : {n | critical C n}.HasDensity 0 := by
  classical
  by_cases hC : C=0
  · subst C
    have he : {n | critical 0 n} = (∅ : Set ℕ) := by
      ext n
      simp [critical]
      omega
    rw [he]
    exact Set.HasDensity.empty
  have hu := (scaled_semiCount_ratio_zero (Nat.pos_of_ne_zero hC)).const_mul
    (2*(C+1:ℕ):ℝ)
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    change {n | critical C n}.partialDensity Set.univ N ≤
      (2*(C+1:ℕ):ℝ)*((semiCount (C*N):ℝ)/N)
    rw [partialDensity_eq_filter_card]
    have hc : (((range N).filter (critical C)).card : ℝ) ≤
        (2*(C+1:ℕ):ℝ)*semiCount (C*N) := by
      exact_mod_cast critical_count_bound C N
    calc
      _ = (((range N).filter (critical C)).card : ℝ)/N := by
        congr 2
        apply congrArg Finset.card
        ext n
        simp
      _ ≤ _ := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc
          (Nat.cast_nonneg (α := ℝ) N)

/-- In particular, the fixed-width band immediately below the threshold is
negligible as well as the previously handled band above it. -/
theorem subcritical_band_hasDensity_zero (C : ℕ) :
    {n | 1 < n ∧ n ≤ C*(P n*P (n+1)) ∧ P n*P (n+1) ≤ n}.HasDensity 0 := by
  by_cases hC : C=0
  · subst C
    apply Erdos371Exploration.density_zero_of_subset (T := {n | critical 0 n})
      _ (critical_hasDensity_zero 0)
    intro n hn
    have := hn.1
    have := hn.2.1
    simp only [zero_mul] at *
    omega
  apply Erdos371Exploration.density_zero_of_subset _ (critical_hasDensity_zero C)
  intro n hn
  exact ⟨hn.1,hn.2.1,hn.2.2.trans (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hC))⟩

end Erdos371CriticalProductBand

#print axioms Erdos371CriticalProductBand.critical_count_bound
#print axioms Erdos371CriticalProductBand.critical_hasDensity_zero
#print axioms Erdos371CriticalProductBand.subcritical_band_hasDensity_zero
