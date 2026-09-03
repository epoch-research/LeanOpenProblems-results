import FormalConjecturesUtil
import Submission.ComparableHighProduct

/-! Fixed-ratio separation of largest prime factors of consecutive integers.
  This is an unsigned density-zero theorem, not a proof of Erdős 371. -/

namespace Erdos371ComparableRatio

open Finset Filter Erdos371Cofactor Erdos371ComparableHighProduct
open Erdos371ComparableLowProduct Erdos371SieveParameters Erdos371SieveScaleBands
open Erdos371ReflectionRange
open scoped Topology

attribute [local instance] Classical.propDecidable

def comparable (L : ℕ) : Set ℕ :=
  {n | 1<n ∧ max (P n) (P (n+1)) ≤ 2^L * min (P n) (P (n+1))}

lemma partialDensity_union_le (S T : Set ℕ) (N : ℕ) :
    (S ∪ T).partialDensity Set.univ N ≤
      S.partialDensity Set.univ N + T.partialDensity Set.univ N := by
  simp only [partialDensity_eq_filter_card, Set.mem_union]
  rw [Finset.filter_or, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_union_le ((Finset.range N).filter fun n => n∈S)
    ((Finset.range N).filter fun n => n∈T)

lemma comparable_eq_union (L M : ℕ) :
    comparable L = closeBelow M L ∪ closeAbove M L := by
  ext n
  simp only [comparable,closeBelow,closeAbove,Set.mem_setOf_eq,Set.mem_union]
  omega

lemma comparable_partialDensity_bound {K L : ℕ} (hLK : L+3≤K) {N : ℕ} (hN : 0<N) :
    (comparable L).partialDensity Set.univ N ≤
      (closeBelow (threshold K) L).partialDensity Set.univ N +
        48*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2 * tail K := by
  rw [comparable_eq_union L (threshold K)]
  exact (partialDensity_union_le _ _ _).trans
    (add_le_add le_rfl (closeAbove_partialDensity_bound hLK hN))

/-- Largest prime factors at consecutive integers have no fixed-ratio
  concentration, outside a set of natural density zero. -/
theorem comparable_hasDensity_zero (L : ℕ) : (comparable L).HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  have ht : Tendsto (fun K => 48*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2 * tail K) atTop (𝓝 0) := by
    simpa only [mul_zero] using tail_tendsto_zero.const_mul (48*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2)
  obtain ⟨K,hK,hsmall⟩ := ((eventually_ge_atTop (L+3)).and
    (ht.eventually_lt_const (half_pos hε))).exists
  have hlo := (closeBelow_hasDensity_zero (threshold K) L).eventually_lt_const (half_pos hε)
  filter_upwards [hlo,eventually_gt_atTop 0] with N hNlo hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  have hh := comparable_partialDensity_bound hK hN
  linarith

/-- An unrestricted fixed-ratio version of the separation theorem. This
  says nothing about which of the two largest prime factors is larger. -/
theorem fixed_ratio_hasDensity_zero (C : ℕ) :
    {n | max (P n) (P (n+1)) ≤ C * min (P n) (P (n+1))}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset
    (T := Erdos371BoundedPrimeGap.lowSet 2 ∪ comparable C)
  · intro n hn
    by_cases h : 1<n
    · apply Or.inr
      refine ⟨h,hn.trans ?_⟩
      exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := C)).le
    · apply Or.inl
      apply Or.inl
      exact Nat.maxPrimeFac_le.trans (by omega : n≤2)
  · exact Erdos371CofactorDensity.density_zero_union
      (Erdos371BoundedPrimeGap.lowSet_hasDensity_zero 2) (comparable_hasDensity_zero C)

end Erdos371ComparableRatio

#print axioms Erdos371ComparableRatio.comparable_hasDensity_zero
#print axioms Erdos371ComparableRatio.fixed_ratio_hasDensity_zero
