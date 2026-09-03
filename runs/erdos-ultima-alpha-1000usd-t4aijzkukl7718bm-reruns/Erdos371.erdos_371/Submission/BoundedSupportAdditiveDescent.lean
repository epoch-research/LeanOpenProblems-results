import FormalConjecturesUtil
import Submission.FiniteSupportAdditiveDescent

/-! Uniform half-descent upper bounds for additive perturbations of a
nonnegative logarithm with a bounded NUMBER of support primes. The primes
and all real coefficients may move with the counting cutoff. The support
cardinality bound is fixed; this does not settle Erdős 371. -/

namespace Erdos371BoundedSupportAdditiveDescent

open Finset Filter Erdos371FiniteSupportAdditiveDescent
open scoped Topology
attribute [local instance] Classical.propDecidable

abbrev smallPrimes (K : ℕ) := (K+1).primesBelow

noncomputable def mask (s : Finset ℕ) (w : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p ∈ s then w p else 0

lemma additive_eq_off_tail {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (K : ℕ) (w : ℕ → ℝ) (n : ℕ)
    (h : ∀ p ∈ s, K<p → ¬p ∣ n) :
    additive (smallPrimes K) (mask s w) n=additive s w n := by
  have he : (smallPrimes K).filter (fun p => p ∈ s)=s.filter (fun p => p ≤ K) := by
    ext p
    simp only [mem_filter,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpK,_⟩,hps⟩
      exact ⟨hps,by omega⟩
    · rintro ⟨hps,hpK⟩
      exact ⟨⟨by omega,hs p hps⟩,hps⟩
  unfold additive mask
  simp only [ite_mul,zero_mul,← sum_filter,he]
  apply sum_subset (filter_subset _ _)
  intro p hp hpnot
  have hpK : K<p := by
    have h : ¬p ≤ K := fun hK => hpnot (mem_filter.mpr ⟨hp,hK⟩)
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd (h p hp hpK)]
  simp

noncomputable def tailCover (s : Finset ℕ) (K N : ℕ) : Finset ℕ :=
  (s.filter (fun p => K<p)).biUnion
    (fun p => (range N).filter (fun n => p ∣ n ∨ p ∣ n+1))

lemma tailCover_card_bound (s : Finset ℕ) (K N : ℕ) :
    (tailCover s K N).card ≤ ∑ p ∈ s.filter (fun p => K<p), (2*(N/p)+1) := by
  exact card_biUnion_le.trans (sum_le_sum fun p _ => either_multiple_count_le p N)

lemma tailCover_real_bound (s : Finset ℕ) (K N : ℕ) :
    ((tailCover s K N).card : ℝ) ≤
      2*(N : ℝ)*(∑ p ∈ s.filter (fun p => K<p), (1 : ℝ)/p)+s.card := by
  have hh := Nat.cast_le (α := ℝ).mpr (tailCover_card_bound s K N)
  push_cast at hh
  apply hh.trans
  calc
    _ ≤ ∑ p ∈ s.filter (fun p => K<p), (2*((N : ℝ)/p)+1) :=
      sum_le_sum fun p _ => add_le_add
        (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) le_rfl
    _ = 2*(N : ℝ)*(∑ p ∈ s.filter (fun p => K<p), (1 : ℝ)/p)+
        (s.filter (fun p => K<p)).card := by
      have he (p : ℕ) : 2*((N : ℝ)/p)=2*(N : ℝ)*((1 : ℝ)/p) := by ring
      simp only [he,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_one]
    _ ≤ _ := add_le_add le_rfl (Nat.cast_le.mpr (card_filter_le _ _))

lemma descent_comparison {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (K N : ℕ) (a : ℝ) (w : ℕ → ℝ) :
    descentCount (height s a w) N ≤
      descentCount (height (smallPrimes K) a (mask s w)) N+(tailCover s K N).card := by
  apply (card_le_card (show (range N).filter (fun n => height s a w (n+1)<height s a w n) ⊆
      (range N).filter (fun n => height (smallPrimes K) a (mask s w) (n+1)<
        height (smallPrimes K) a (mask s w) n) ∪ tailCover s K N from ?_)).trans
      (card_union_le _ _)
  intro n hn
  obtain ⟨hnN,hd⟩ := mem_filter.mp hn
  by_cases hnT : n ∈ tailCover s K N
  · exact mem_union_right _ hnT
  · have h (p : ℕ) (hp : p ∈ s) (hpK : K<p) : ¬p ∣ n ∧ ¬p ∣ n+1 := by
      constructor
      · intro hh
        exact hnT (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨hp,hpK⟩,
          mem_filter.mpr ⟨hnN,Or.inl hh⟩⟩)
      · intro hh
        exact hnT (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨hp,hpK⟩,
          mem_filter.mpr ⟨hnN,Or.inr hh⟩⟩)
    have he₁ := additive_eq_off_tail hs K w n (fun p hp hpK => (h p hp hpK).1)
    have he₂ := additive_eq_off_tail hs K w (n+1) (fun p hp hpK => (h p hp hpK).2)
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨hnN,?_⟩
    simpa only [height,he₁,he₂] using hd

lemma descent_ratio_comparison {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (K : ℕ) {N : ℕ} (hN : 0<N) (a : ℝ) (w : ℕ → ℝ) :
    (descentCount (height s a w) N : ℝ)/N ≤
      (descentCount (height (smallPrimes K) a (mask s w)) N : ℝ)/N+
      2*(∑ p ∈ s.filter (fun p => K<p), (1 : ℝ)/p)+(s.card : ℝ)/N := by
  have hc := Nat.cast_le (α := ℝ).mpr (descent_comparison hs K N a w)
  push_cast at hc
  have hb := tailCover_real_bound s K N
  have hh := div_le_div_of_nonneg_right (hc.trans (add_le_add le_rfl hb))
    (Nat.cast_nonneg (α := ℝ) N)
  apply hh.trans_eq
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

lemma bounded_card_tail {s : Finset ℕ} {B K : ℕ} (hB : s.card ≤ B) (hK : 0<K) :
    (∑ p ∈ s.filter (fun p => K<p), (1 : ℝ)/p) ≤ (B : ℝ)/K := by
  calc
    _ ≤ ∑ _p ∈ s.filter (fun p => K<p), (1 : ℝ)/K := by
      apply sum_le_sum
      intro p hp
      have hkp := (mem_filter.mp hp).2.le
      exact div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hkp)
    _ = ((s.filter (fun p => K<p)).card : ℝ)/K := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right
      (Nat.cast_le.mpr ((card_filter_le _ _).trans hB)) (Nat.cast_nonneg (α := ℝ) K)

/-- For a fixed cardinality bound, the support primes themselves may vary
arbitrarily with the cutoff, as may all the coefficients. -/
theorem uniform_bounded_support_bound (B : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ℕ) (a : ℝ) (w : ℕ → ℝ),
      (∀ p ∈ s, p.Prime) → s.card ≤ B → 0 ≤ a →
      (descentCount (height s a w) N : ℝ)/N ≤ 1/2+ε := by
  have hthird : (0 : ℝ)<ε/3 := by positivity
  obtain ⟨K,hK,hKB⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat (2*(B : ℝ))).eventually
      (gt_mem_nhds hthird))).exists
  have hs := uniform_finite_support_bound
    (s := smallPrimes K) (fun p hp => Nat.prime_of_mem_primesBelow hp) (ε/3) hthird
  have hBsmall := (tendsto_const_div_atTop_nhds_zero_nat (B : ℝ)).eventually
    (gt_mem_nhds hthird)
  filter_upwards [hs,hBsmall,eventually_gt_atTop 0] with N hsmall hBN hN
  intro s a w hsp hsB ha
  have hc := descent_ratio_comparison hsp K hN a w
  have ht := bounded_card_tail hsB hK
  have hbase := hsmall a (mask s w) ha
  have hcard := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hsB)
    (Nat.cast_nonneg (α := ℝ) N)
  change 2*(B : ℝ)/K<ε/3 at hKB
  rw [mul_div_assoc] at hKB
  linarith

end Erdos371BoundedSupportAdditiveDescent

#print axioms Erdos371BoundedSupportAdditiveDescent.uniform_bounded_support_bound
