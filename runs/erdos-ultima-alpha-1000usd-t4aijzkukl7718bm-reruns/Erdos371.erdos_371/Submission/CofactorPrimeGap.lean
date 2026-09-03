import FormalConjecturesUtil
import Submission.ComparableRatio

/-! Separation between the largest prime factor and the largest prime factor
  of its cofactor, including repeated largest prime factors. -/

namespace Erdos371CofactorPrimeGap

open Finset Filter Erdos371Cofactor Erdos371PrimeHarmonicBlocks
open Erdos371ReflectionRange Erdos371ComparableLowProduct
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def multiples (p q N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun n => n ≠ 0 ∧ p*q ∣ n

lemma multiples_card_bound (p q N : ℕ) :
    (multiples p q N).card ≤ (N:ℝ)/((p:ℝ)*q) := by
  unfold multiples
  rw [Nat.card_multiples']
  simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := N) (n := p*q))

noncomputable def pairCover (k j N : ℕ) : Finset ℕ :=
  (block k).biUnion fun p => (block j).biUnion fun q => multiples p q N

lemma pairCover_bound (k j N : ℕ) : (pairCover k j N).card ≤ (N:ℝ)*pairMass k j := by
  have hc : (pairCover k j N).card ≤
      ∑ p ∈ block k, ∑ q ∈ block j, (multiples p q N).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
  calc
    _ ≤ ∑ p ∈ block k, ∑ q ∈ block j, ((multiples p q N).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ p ∈ block k, ∑ q ∈ block j, (N:ℝ)/((p:ℝ)*q) :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => multiples_card_bound _ _ _))
    _ = _ := by simp [pairMass, Finset.mul_sum, div_eq_mul_inv]

noncomputable def cover (L K T N : ℕ) : Finset ℕ :=
  (Finset.Ico K T).biUnion fun k => (Finset.Icc k (k+L)).biUnion fun j => pairCover k j N

lemma cover_bound {K : ℕ} (hK : 0<K) (L T N : ℕ) :
    (cover L K T N).card ≤ 32*(L+1:ℕ)*(N:ℝ)/(K:ℝ) := by
  have hc : (cover L K T N).card ≤
      ∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), (pairCover k j N).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), ((pairCover k j N).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), (N:ℝ)*pairMass k j :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => pairCover_bound _ _ _))
    _ = (N:ℝ)*(∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), pairMass k j) := by
      simp [Finset.mul_sum]
    _ ≤ (N:ℝ)*(32*(L+1:ℕ)/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left (nearby_blocks_tail_bound hK L T) (by positivity)
    _ = _ := by ring

def bad (L : ℕ) : Set ℕ := {n | 1<n ∧ P n ≤ 2^L*P (cofactor n)}

lemma mem_cover {L K N n : ℕ} (hnN : n<N) (hn : n ∈ bad L)
    (hbig : 2^(K+L)<P n) : n ∈ cover L K (N+1) N := by
  have hn1 : 1<n := hn.1
  let p := P (cofactor n)
  let q := P n
  have hpbig : 2^K<p := by
    have hh := hn.2
    rw [pow_add] at hbig
    by_contra h
    have he := Nat.mul_le_mul_left (2^L) (Nat.le_of_not_gt h)
    dsimp [p] at he
    nlinarith
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt _ (by
    have h2 := Nat.one_le_two_pow (n := K)
    have hle : p≤cofactor n := Nat.maxPrimeFac_le
    omega)
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn.1
  have hpd : p∣cofactor n := Nat.maxPrimeFac_dvd
  have hprod : p*q ∣ n := by
    have hh := Nat.mul_dvd_mul_right hpd q
    simpa only [q, cofactor_mul] using hh
  have hpq : p≤q := Nat.le_maxPrimeFac (by omega : n≠0) hp
    ((dvd_mul_right p q).trans hprod)
  let k := Nat.log 2 p
  let j := Nat.log 2 q
  have hpk : p∈block k := block_of_log hp
  have hqj : q∈block j := block_of_log hq
  have hKk : K≤k := Nat.le_log_of_pow_le (by decide) hpbig.le
  have hkN : k<N+1 := by
    have hlog := Nat.log_le_self 2 p
    have hple : p≤N := hpq.trans (Nat.maxPrimeFac_le.trans hnN.le)
    dsimp [k]
    omega
  have hkj : k≤j := Nat.log_mono_right hpq
  have hjk : j≤k+L := by
    have hqpow := (mem_block.mp hqj).2.1
    have hplt := (mem_block.mp hpk).2.2
    have hh := Nat.mul_lt_mul_of_pos_left hplt (Nat.two_pow_pos L)
    have he : 2^L*2^(k+1)=2^(k+L+1) := by rw [← pow_add]; congr 1; omega
    rw [he] at hh
    have hr : q≤2^L*p := hn.2
    have hpow : 2^j<2^(k+L+1) := hqpow.trans_lt (hr.trans_lt hh)
    have ht := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp hpow
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨k,Finset.mem_Ico.mpr ⟨hKk,hkN⟩,Finset.mem_biUnion.mpr ?_⟩
  refine ⟨j,Finset.mem_Icc.mpr ⟨hkj,hjk⟩,Finset.mem_biUnion.mpr ?_⟩
  refine ⟨p,hpk,Finset.mem_biUnion.mpr ⟨q,hqj,?_⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,hprod⟩

lemma bad_partialDensity_bound {K N : ℕ} (hK : 0<K) (hN : 0<N) (L : ℕ) :
    (bad L).partialDensity Set.univ N ≤
      {n | P n≤2^(K+L)}.partialDensity Set.univ N + 32*(L+1:ℕ)/(K:ℝ) := by
  let G := (Finset.range N).filter fun n => n∈bad L
  let B := (Finset.range N).filter fun n => n ∈ {m | P m≤2^(K+L)}
  have hsub : G ⊆ B ∪ cover L K (N+1) N := by
    intro n hn
    obtain ⟨hnN,hn⟩ := Finset.mem_filter.mp hn
    by_cases h : P n≤2^(K+L)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnN,h⟩)
    · exact Finset.mem_union_right _ (mem_cover (Finset.mem_range.mp hnN) hn (by omega))
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcr : (G.card:ℝ) ≤ B.card + 32*(L+1:ℕ)*(N:ℝ)/(K:ℝ) := by
    have hh : (G.card:ℝ) ≤ B.card + (cover L K (N+1) N).card := by exact_mod_cast hc
    linarith [cover_bound hK L (N+1) N]
  rw [partialDensity_eq_filter_card,partialDensity_eq_filter_card]
  simp only [Set.mem_setOf_eq]
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hfinal : (G.card:ℝ)/N ≤ (B.card:ℝ)/N + 32*(L+1:ℕ)/(K:ℝ) := by
    calc
      _ ≤ ((B.card:ℝ)+32*(L+1:ℕ)*(N:ℝ)/(K:ℝ))/N :=
        div_le_div_of_nonneg_right hcr (by positivity)
      _ = _ := by field_simp
  convert hfinal using 1 <;> dsimp only [G,B]
  congr 3
  all_goals congr

lemma bad_hasDensity_zero (L : ℕ) : (bad L).HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  have ht := tendsto_const_div_atTop_nhds_zero_nat (32*(L+1:ℕ):ℝ)
  obtain ⟨K,hK,hsmall⟩ := ((eventually_gt_atTop 0).and
    (ht.eventually_lt_const (half_pos hε))).exists
  have hlo := (Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero (2^(K+L))).eventually_lt_const (half_pos hε)
  filter_upwards [hlo,eventually_gt_atTop 0] with N hloN hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  have hh := bad_partialDensity_bound hK hN L
  linarith

/-- The cofactor contains no prime comparable to the largest prime factor,
  except on a density-zero set. This includes repeated largest factors. -/
theorem fixed_ratio_cofactor_hasDensity_zero (C : ℕ) :
    {n | 1<n ∧ P n ≤ C*P (cofactor n)}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset (T := bad C) _ (bad_hasDensity_zero C)
  intro n hn
  exact ⟨hn.1, hn.2.trans (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := C)).le)⟩

end Erdos371CofactorPrimeGap

#print axioms Erdos371CofactorPrimeGap.fixed_ratio_cofactor_hasDensity_zero
