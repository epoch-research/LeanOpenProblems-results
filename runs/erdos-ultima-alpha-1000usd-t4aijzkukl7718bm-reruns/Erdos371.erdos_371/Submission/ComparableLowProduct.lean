import FormalConjecturesUtil
import Submission.PrimeHarmonicBlocks
import Submission.ReflectionRange

/-! Comparable adjacent largest prime factors are rare when their product is
at most a fixed multiple of the input. The larger-product region is not settled here. -/

namespace Erdos371ComparableLowProduct

open Erdos371Cofactor Erdos371PrimeHarmonicBlocks Erdos371BoundedPrimeGap
open Erdos371ReflectionRange
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def pairSolutions (p q A N : ℕ) : Finset ℕ :=
  if p.Coprime q ∧ p*q ≤ A*N then solutions p q N ∪ solutions q p N else ∅

lemma pairSolutions_card_bound {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (A N : ℕ) :
    ((pairSolutions p q A N).card : ℝ) ≤ 2*(A+1:ℕ)*(N:ℝ)/((p:ℝ)*q) := by
  have hpq : (0:ℝ) < (p:ℝ)*q := by positivity
  unfold pairSolutions
  split_ifs with h
  · obtain ⟨hcop, hbound⟩ := h
    have hc : (solutions p q N ∪ solutions q p N).card ≤ 2*(N/(p*q)+1) := by
      have h1 := solutions_card_le hcop N
      have h2 := solutions_card_le hcop.symm N
      have hh := Finset.card_union_le (solutions p q N) (solutions q p N)
      rw [Nat.mul_comm q p] at h2
      omega
    have hdiv : ((N/(p*q):ℕ):ℝ) ≤ (N:ℝ)/((p:ℝ)*q) := by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := p*q))
    have hb : (p:ℝ)*q ≤ (A:ℝ)*N := by exact_mod_cast hbound
    have hone : (1:ℝ) ≤ (A:ℝ)*N/((p:ℝ)*q) := (le_div_iff₀ hpq).mpr (by simpa using hb)
    calc
      _ ≤ 2*(((N/(p*q):ℕ):ℝ)+1) := by exact_mod_cast hc
      _ ≤ 2*((N:ℝ)/((p:ℝ)*q)+(A:ℝ)*N/((p:ℝ)*q)) := by linarith
      _ = _ := by push_cast; ring
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity

noncomputable def pairCover (A k j N : ℕ) : Finset ℕ :=
  (block k).biUnion fun p => (block j).biUnion fun q => pairSolutions p q A N

lemma pairCover_card_bound (A k j N : ℕ) :
    ((pairCover A k j N).card : ℝ) ≤ 2*(A+1:ℕ)*(N:ℝ) * pairMass k j := by
  have hc : (pairCover A k j N).card ≤
      ∑ p ∈ block k, ∑ q ∈ block j, (pairSolutions p q A N).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun p _ => Finset.card_biUnion_le)
  calc
    _ ≤ ∑ p ∈ block k, ∑ q ∈ block j, ((pairSolutions p q A N).card:ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ p ∈ block k, ∑ q ∈ block j, 2*(A+1:ℕ)*(N:ℝ)/((p:ℝ)*q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact pairSolutions_card_bound (mem_block.mp hp).1.pos (mem_block.mp hq).1.pos A N
    _ = _ := by simp [pairMass, Finset.mul_sum, div_eq_mul_inv]

noncomputable def fullCover (A L K T N : ℕ) : Finset ℕ :=
  (Finset.Ico K T).biUnion fun k =>
    (Finset.Icc k (k+L)).biUnion fun j => pairCover A k j N

lemma fullCover_card_bound {K : ℕ} (hK : 0 < K) (A L T N : ℕ) :
    ((fullCover A L K T N).card : ℝ) ≤ 64*(A+1:ℕ)*(L+1:ℕ)*(N:ℝ)/K := by
  have hc : (fullCover A L K T N).card ≤
      ∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), (pairCover A k j N).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun k _ => Finset.card_biUnion_le)
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), ((pairCover A k j N).card:ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L),
        2*(A+1:ℕ)*(N:ℝ) * pairMass k j := by
      exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun j _ => pairCover_card_bound A k j N))
    _ = 2*(A+1:ℕ)*(N:ℝ) *
        (∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), pairMass k j) := by
      simp [Finset.mul_sum]
    _ ≤ 2*(A+1:ℕ)*(N:ℝ) * (32*(L+1:ℕ)/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left (nearby_blocks_tail_bound hK L T) (by positivity)
    _ = _ := by ring

def closeBelow (A L : ℕ) : Set ℕ :=
  {n | 1 < n ∧ max (P n) (P (n+1)) ≤ 2^L * min (P n) (P (n+1)) ∧
    P n * P (n+1) ≤ A*(n+1)}

lemma block_of_log {p : ℕ} (hp : p.Prime) : p ∈ block (Nat.log 2 p) := by
  exact mem_block.mpr ⟨hp, Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by decide) p⟩

lemma mem_fullCover {n N A L K : ℕ} (hnN : n < N) (hn : n ∈ closeBelow A L)
    (hlarge : 2^K ≤ min (P n) (P (n+1))) : n ∈ fullCover A L K (N+1) N := by
  obtain ⟨hn1, hratio, hprod⟩ := hn
  let p := min (P n) (P (n+1))
  let q := max (P n) (P (n+1))
  let k := Nat.log 2 p
  let j := Nat.log 2 q
  have hp0 := Nat.prime_maxPrimeFac_of_one_lt n hn1
  have hq0 := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega : 1 < n+1)
  have hp : p.Prime := by dsimp [p]; rcases min_choice (P n) (P (n+1)) with h | h <;> rwa [h]
  have hq : q.Prime := by dsimp [q]; rcases max_choice (P n) (P (n+1)) with h | h <;> rwa [h]
  have hpk : p ∈ block k := block_of_log hp
  have hqj : q ∈ block j := block_of_log hq
  have hpq : p ≤ q := min_le_max
  have hkj : k ≤ j := Nat.log_mono_right hpq
  have hKk : K ≤ k := Nat.le_log_of_pow_le (by decide) hlarge
  have hkN : k < N+1 := by
    have hh := Nat.log_le_self 2 p
    have hpN : p ≤ N := (min_le_left _ _).trans (Nat.maxPrimeFac_le.trans hnN.le)
    dsimp [k]
    omega
  have hjk : j ≤ k+L := by
    have hqpow : 2^j ≤ q := (mem_block.mp hqj).2.1
    have hplt : p < 2^(k+1) := (mem_block.mp hpk).2.2
    have hmul := Nat.mul_lt_mul_of_pos_left hplt (Nat.two_pow_pos L)
    have hr : q ≤ 2^L*p := hratio
    have he : 2^L * 2^(k+1) = 2^(k+L+1) := by rw [← pow_add]; congr 1; omega
    rw [he] at hmul
    have ht : 2^j < 2^(k+L+1) := hqpow.trans_lt (hr.trans_lt hmul)
    have hh := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mp ht
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_Ico.mpr ⟨hKk, hkN⟩, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨j, Finset.mem_Icc.mpr ⟨hkj, hjk⟩, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨p, hpk, Finset.mem_biUnion.mpr ⟨q, hqj, ?_⟩⟩
  have hne := Erdos371PrimeDiscrepancy.consecutive_ne n
  change P (n+1) ≠ P n at hne
  have hneq : p ≠ q := by dsimp [p,q]; omega
  have hcop := (Nat.coprime_primes hp hq).mpr hneq
  have hpqN : p*q ≤ A*N := by
    dsimp [p,q]
    rw [min_mul_max]
    exact hprod.trans (Nat.mul_le_mul_left A (by omega))
  rw [pairSolutions, if_pos ⟨hcop, hpqN⟩]
  have hpn : P n ∣ n := Nat.maxPrimeFac_dvd
  have hqn : P (n+1) ∣ n+1 := Nat.maxPrimeFac_dvd
  by_cases h : P n ≤ P (n+1)
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hnN, by simpa [p, min_eq_left h] using hpn,
      by simpa [q, max_eq_right h] using hqn⟩
  · have hh : P (n+1) ≤ P n := by omega
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hnN, by simpa [q, max_eq_left hh] using hpn,
      by simpa [p, min_eq_right hh] using hqn⟩


lemma partialDensity_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (A L : ℕ) :
    (closeBelow A L).partialDensity Set.univ N ≤
      (lowSet (2^K)).partialDensity Set.univ N + 64*(A+1:ℕ)*(L+1:ℕ)/(K:ℝ) := by
  let G := (Finset.range N).filter fun n => n ∈ closeBelow A L
  let B := (Finset.range N).filter fun n => n ∈ lowSet (2^K)
  have hsub : G ⊆ B ∪ fullCover A L K (N+1) N := by
    intro n hn
    simp only [G, Finset.mem_filter, Finset.mem_range] at hn
    by_cases hb : n ∈ lowSet (2^K)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.1, hb⟩)
    · apply Finset.mem_union_right
      apply mem_fullCover hn.1 hn.2
      change ¬(P n ≤ 2^K ∨ P (n+1) ≤ 2^K) at hb
      omega
  have hc : (G.card:ℝ) ≤ B.card + 64*(A+1:ℕ)*(L+1:ℕ)*(N:ℝ)/(K:ℝ) := by
    have hh : G.card ≤ B.card + (fullCover A L K (N+1) N).card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact (Nat.cast_le.mpr hh).trans (by
      push_cast
      have hb := fullCover_card_bound hK A L (N+1) N
      push_cast at hb
      linarith)
  rw [partialDensity_eq_filter_card, partialDensity_eq_filter_card]
  change (G.card:ℝ)/N ≤ (B.card:ℝ)/N + _
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  calc
    _ ≤ ((B.card:ℝ) + 64*(A+1:ℕ)*(L+1:ℕ)*(N:ℝ)/(K:ℝ))/N :=
      div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)
    _ = _ := by field_simp

/-- This only concerns the fixed-linear-product region. No orientation
balance and no estimate in the complementary region is asserted. -/
theorem closeBelow_hasDensity_zero (A L : ℕ) : (closeBelow A L).HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  have ht := tendsto_const_div_atTop_nhds_zero_nat (64*(A+1:ℕ)*(L+1:ℕ):ℝ)
  obtain ⟨K, hK, hk⟩ := ((eventually_gt_atTop 0).and
    (ht.eventually_lt_const (half_pos hε))).exists
  have hb := (lowSet_hasDensity_zero (2^K)).eventually_lt_const (half_pos hε)
  filter_upwards [hb, eventually_gt_atTop 0] with N hbN hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  have hh := partialDensity_bound hK hN A L
  linarith

/-- Adjacent largest prime factors cannot stay within a fixed ratio while
their product stays below a fixed multiple of the input, except on a set
of natural density zero. -/
theorem fixed_ratio_low_product_hasDensity_zero (A C : ℕ) :
    {n | 1 < n ∧ max (P n) (P (n+1)) ≤ C * min (P n) (P (n+1)) ∧
      P n * P (n+1) ≤ A*(n+1)}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset _ (closeBelow_hasDensity_zero A C)
  intro n hn
  refine ⟨hn.1, hn.2.1.trans ?_, hn.2.2⟩
  exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := C)).le

end Erdos371ComparableLowProduct

#print axioms Erdos371ComparableLowProduct.fullCover_card_bound
#print axioms Erdos371ComparableLowProduct.mem_fullCover
#print axioms Erdos371ComparableLowProduct.closeBelow_hasDensity_zero
#print axioms Erdos371ComparableLowProduct.fixed_ratio_low_product_hasDensity_zero
