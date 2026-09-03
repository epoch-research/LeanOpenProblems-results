import Submission.UniformEvenMean
import Submission.EnvelopeFactorBounds

/-! A restricted fractional-mean comparison. No unbounded-count rounding
principle or solution of Erdos 184 is asserted in this file. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LowCountMean
open FractionalCycles FractionalEnvelope CountCritical CycleNumberSubmodularity
open UniformEvenMean
variable {V : Type*} [Fintype V]
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

/-- Two edge-disjoint cycles force fractional cost at least two, even when
there are other edges in the ambient even graph. -/
lemma two_le_optimum_of_two_cycles {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (H K : CyclePiece G)
    (hd : Disjoint H.val.edgeSet K.val.edgeSet) : 2 ≤ optimum G := by
  by_cases hlarge : ∃ v, 4 ≤ G.degree v
  · obtain ⟨v,hv⟩ := hlarge
    have hh := degree_le_twice_optimum G he v
    have hv' : (4 : ℝ) ≤ G.degree v := by exact_mod_cast hv
    linarith
  have hdeg : ∀ v, G.degree v ≤ 2 := by
    intro v
    have hn : ¬ 4 ≤ G.degree v := fun h => hlarge ⟨v,h⟩
    obtain ⟨r,hr⟩ := he v
    omega
  have hg := EnvelopeFactorBounds.cycles_of_even_degree_le_two he hdeg
  have hcov : H.val.spanningCoe.edgeSet ∪ (G \ H.val.spanningCoe).edgeSet = G.edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel H.val.edgeSet_subset
  have hov : (H.val.spanningCoe.support ∩ (G \ H.val.spanningCoe).support).ncard ≤ 1 := by
    rw [Set.disjoint_iff_inter_eq_empty.mp (CycleFactors.cycle_residual_support_disjoint hg H)]
    simp
  obtain ⟨e,heH⟩ := cycle_edgeSet_nonempty H.val H.property.1 H.property.2
  obtain ⟨f,hfK⟩ := cycle_edgeSet_nonempty K.val K.property.1 K.property.2
  obtain ⟨t,ht,hcost⟩ := optimum_attained G he
  rw [← hcost]
  apply SmallSlackExact.two_edges_lower G t ht e f
    (H.val.edgeSet_subset heH) (K.val.edgeSet_subset hfK)
  intro J ⟨heJ,hfJ⟩
  rcases cycle_contained_in_one_vertex_separation hcov hov J.val
    J.property.1 J.property.2 with hJ | hJ
  · exact Set.disjoint_left.mp hd (hJ hfJ) hfK
  · have hh := hJ heJ
    rw [edgeSet_sdiff] at hh
    exact hh.2 heH

lemma two_le_optimum_of_packing {G : SimpleGraph V}
    (he : ∀ v, Even (G.degree v)) (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet))
    (hs : 2 ≤ S.card) : 2 ≤ optimum G := by
  obtain ⟨H,hH,K,hK,hne⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  exact two_le_optimum_of_two_cycles he ⟨H,hc H hH⟩ ⟨K,hc K hK⟩ (hd hH hK hne)

lemma two_le_optimum_union {G : SimpleGraph V} (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet))
    (hs : 2 ≤ S.card) : 2 ≤ optimum (unionPieces G S) := by
  obtain ⟨H,hH,K,hK,hne⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  exact two_le_optimum_of_two_cycles (SmallSlackExact.union_even S hc hd)
    (SmallSlackExact.unionCycle S hc ⟨H,hH⟩)
    (SmallSlackExact.unionCycle S hc ⟨K,hK⟩) (hd hH hK hne)

lemma union_ne_bot_of_two {G : SimpleGraph V} (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet))
    (hs : 2 ≤ S.card) : unionPieces G S ≠ ⊥ := by
  have hh := two_le_optimum_union S hc hd hs
  intro hb
  rw [hb,optimum_bot] at hh
  norm_num at hh

omit [Fintype V] in
lemma union_complement {G : SimpleGraph V} (D S : Finset G.Subgraph)
    (hd : IsDecomposition G D) (hS : S ⊆ D) :
    unionPieces G (D \ S) = G \ unionPieces G S := by
  apply edgeSet_injective
  rw [unionPieces_edgeSet,edgeSet_sdiff,unionPieces_edgeSet,← hd.2]
  ext e
  constructor
  · intro h
    obtain ⟨H,hH,he⟩ := Set.mem_iUnion₂.mp h
    refine ⟨Set.mem_iUnion₂.mpr ⟨H,(Finset.mem_sdiff.mp hH).1,he⟩,?_⟩
    intro hh
    obtain ⟨K,hK,hf⟩ := Set.mem_iUnion₂.mp hh
    have hne : H ≠ K := by
      intro heq
      exact (Finset.mem_sdiff.mp hH).2 (heq ▸ hK)
    exact Set.disjoint_left.mp (hd.1 (Finset.mem_sdiff.mp hH).1 (hS hK) hne) he hf
  · rintro ⟨h,hn⟩
    obtain ⟨H,hH,he⟩ := Set.mem_iUnion₂.mp h
    exact Set.mem_iUnion₂.mpr ⟨H,Finset.mem_sdiff.mpr ⟨hH,fun hHS =>
      hn (Set.mem_iUnion₂.mpr ⟨H,hHS,he⟩)⟩,he⟩

lemma exists_large_partition {G : SimpleGraph V} (hG : IsCountCritical 3 G)
    (hi : ¬ InvariantPartitions.HasInvariantCount G) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ 4 ≤ D.card := by
  by_contra! hn
  apply hi
  intro D E hcD hdD hcE hdE
  have hlD := number_le G D hcD hdD
  have hlE := number_le G E hcE hdE
  have huD := hn D hcD hdD
  have huE := hn E hcE hdE
  rw [hG.2.1] at hlD hlE
  omega

lemma sum_lower_of_two_exceptions {α : Type*} (s : Finset α) (c : α → ℝ)
    (k : ℝ) (a b p q : α) (ha : a ∈ s) (hb : b ∈ s)
    (hp : p ∈ s) (hq : q ∈ s) (hab : a ≠ b)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q)
    (hbase : ∀ x ∈ s, x ≠ p → x ≠ q → k ≤ c x)
    (hca : k+1 ≤ c a) (hcb : k+1 ≤ c b)
    (hcp : k-1 ≤ c p) (hcq : k-1 ≤ c q) :
    k * s.card ≤ ∑ x ∈ s, c x := by
  classical
  have hpoint (x : α) (hx : x ∈ s) :
      k + (if x = a then 1 else 0) + (if x = b then 1 else 0) ≤
      c x + (if x = p then 1 else 0) + (if x = q then 1 else 0) := by
    by_cases hxp : x = p
    · subst x
      by_cases hpq : p = q <;> simp [Ne.symm hap,Ne.symm hbp,Ne.symm haq,Ne.symm hbq,hpq] <;> linarith
    by_cases hxq : x = q
    · subst x
      simp [Ne.symm haq,Ne.symm hbq,hxp]
      linarith
    by_cases hxa : x = a
    · subst x
      simpa [hxp,hxq,hab] using hca
    by_cases hxb : x = b
    · subst x
      simpa [hxp,hxq,hxa] using hcb
    simpa [hxp,hxq,hxa,hxb] using hbase x hx hxp hxq
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
    Finset.sum_ite_eq',if_pos ha,if_pos hb,if_pos hp,if_pos hq] at hh
  linarith

omit [Fintype V] in
lemma ne_complement_of_ne_bot {G A : SimpleGraph V} (hA : A ≠ ⊥) : A ≠ G \ A := by
  intro h
  apply hA
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have hh : (G \ A).Adj u v := h ▸ huv
  exact hh.2 huv

/-- Two complementary proper restrictions with one unit of surplus pay
for the two exceptional summands, provided proper restrictions are exact.
This is a criterion, not a claim that its hypotheses hold in general. -/
lemma mean_comparison_of_exact_proper {G : SimpleGraph V} {k : ℕ}
    (he : ∀ v, Even (G.degree v)) (hk : cycleNumber G = k)
    (hex : ∀ H ∈ CycleEnvelope.evenSubgraphs G, H ≠ G →
      optimum H = (cycleNumber H : ℝ))
    (hlow : (k : ℝ)-1 ≤ optimum G)
    (A : SimpleGraph V) (hAm : A ∈ CycleEnvelope.evenSubgraphs G)
    (hA0 : A ≠ ⊥) (hAG : A ≠ G)
    (hboost : (k : ℝ)+1 ≤ optimum A + optimum (G \ A)) :
    (k : ℝ) ≤ 2 * fractionalMean G := by
  let B := G \ A
  have hBm : B ∈ CycleEnvelope.evenSubgraphs G := complement_mem he hAm
  have hAB : A ≠ B := ne_complement_of_ne_bot hA0
  have hcomp : G \ B = A := complement_complement (CycleEnvelope.mem_evenSubgraphs.mp hAm).1
  have hB0 : B ≠ ⊥ := by
    intro h
    have hh := hcomp
    rw [h,sdiff_bot] at hh
    exact hAG hh.symm
  have hBG : B ≠ G := by
    intro h
    have hh := hcomp
    rw [h,sdiff_self] at hh
    exact hA0 hh.symm
  have hGm : G ∈ CycleEnvelope.evenSubgraphs G :=
    CycleEnvelope.mem_evenSubgraphs.mpr ⟨le_rfl,he⟩
  have h0m : (⊥ : SimpleGraph V) ∈ CycleEnvelope.evenSubgraphs G :=
    CycleEnvelope.mem_evenSubgraphs.mpr ⟨bot_le,by
      intro v
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      simp⟩
  let c (H : SimpleGraph V) := optimum H + optimum (G \ H)
  have hbase (H : SimpleGraph V) (hHm : H ∈ CycleEnvelope.evenSubgraphs G)
      (hH0 : H ≠ ⊥) (hHG : H ≠ G) : (k : ℝ) ≤ c H := by
    have hR : G \ H ≠ G := by
      intro h
      have hh := complement_complement (CycleEnvelope.mem_evenSubgraphs.mp hHm).1
      rw [h,sdiff_self] at hh
      exact hH0 hh.symm
    have hb := number_le_complement_sum G he H hHm
    rw [hk] at hb
    dsimp only [c]
    rw [hex H hHm hHG,hex (G \ H) (complement_mem he hHm) hR]
    exact_mod_cast hb
  have hh := sum_lower_of_two_exceptions (CycleEnvelope.evenSubgraphs G) c (k : ℝ)
    A B ⊥ G hAm hBm h0m hGm hAB hA0 hAG hB0 hBG hbase hboost
    (by dsimp only [c]; rw [hcomp]; simpa [B,add_comm] using hboost)
    (by simpa [c,optimum_bot] using hlow)
    (by simpa [c,optimum_bot] using hlow)
  dsimp only [c] at hh
  rw [Finset.sum_add_distrib,sum_complement G he optimum] at hh
  have hp : (0 : ℝ) < (CycleEnvelope.evenSubgraphs G).card := by
    exact_mod_cast card_pos G
  unfold fractionalMean mean
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  linarith

/-- The previously proposed mean comparison holds at count three when the
critical graph is not invariant. The invariant case is not included. -/
lemma noninvariant_count_three {G : SimpleGraph V} (hG : IsCountCritical 3 G)
    (hi : ¬ InvariantPartitions.HasInvariantCount G) : 3 ≤ 2 * fractionalMean G := by
  obtain ⟨D,hc,hd,hcard⟩ := exists_large_partition hG hi
  obtain ⟨S,hSD,hS⟩ := Finset.exists_subset_card_eq (show 2 ≤ D.card by omega)
  let T := D \ S
  have hTD : T ⊆ D := Finset.sdiff_subset
  have hT : 2 ≤ T.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hSD
    dsimp only [T]
    omega
  have hcS : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (hSD hH)
  have hcT : ∀ H ∈ T, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (hTD hH)
  have hdS : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hSD hH) (hSD hK) hne
  have hdT : Set.PairwiseDisjoint (T : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hTD hH) (hTD hK) hne
  let A := unionPieces G S
  have hA0 : A ≠ ⊥ := union_ne_bot_of_two S hcS hdS (by omega)
  have hAc : unionPieces G T = G \ A := union_complement D S hd hSD
  have hAG : A ≠ G := by
    intro h
    have hh := union_ne_bot_of_two T hcT hdT hT
    rw [hAc,h,sdiff_self] at hh
    exact hh rfl
  have hAm : A ∈ CycleEnvelope.evenSubgraphs G :=
    CycleEnvelope.mem_evenSubgraphs.mpr ⟨unionPieces_le G S,
      SmallSlackExact.union_even S hcS hdS⟩
  have hboost : (3 : ℝ)+1 ≤ optimum A + optimum (G \ A) := by
    have h₁ := two_le_optimum_union S hcS hdS (show 2 ≤ S.card by omega)
    have h₂ := two_le_optimum_union T hcT hdT hT
    rw [hAc] at h₂
    change 2 ≤ optimum A at h₁
    linarith
  have hlow : (3 : ℝ)-1 ≤ optimum G := by
    have hh := two_le_optimum_of_packing hG.1 D hc hd.1 (by omega)
    linarith
  apply mean_comparison_of_exact_proper hG.1 hG.2.1 _ hlow A hAm hA0 hAG hboost
  intro H hHm hHG
  obtain ⟨hHG',heH⟩ := CycleEnvelope.mem_evenSubgraphs.mp hHm
  apply LowCountCritical.optimum_eq_number_of_number_le_two heH
  have hh := hG.2.2 H hHG' hHG heH
  omega

/-- At counts at most two the comparison follows from own fractional
exactness; criticality is not needed. -/
lemma count_le_two {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hk : cycleNumber G ≤ 2) :
    (cycleNumber G : ℝ) ≤ 2 * fractionalMean G := by
  have hh := optimum_le_twice_fractionalMean G he
  rwa [LowCountCritical.optimum_eq_number_of_number_le_two he hk] at hh

/-- Any failure of the coefficient-two mean comparison at critical count
at most three would be invariant, at count exactly three, and fractionally
inexact. No nonexistence of this remaining case is assumed. -/
lemma low_count_failure {G : SimpleGraph V} {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3)
    (hfail : 2 * fractionalMean G < (k : ℝ)) :
    k = 3 ∧ InvariantPartitions.HasInvariantCount G ∧ optimum G < (k : ℝ) := by
  have hk3 : k = 3 := by
    by_contra hn
    have hh := count_le_two hG.1 (by rw [hG.2.1]; omega)
    rw [hG.2.1] at hh
    linarith
  refine ⟨hk3,?_,(optimum_le_twice_fractionalMean G hG.1).trans_lt hfail⟩
  by_contra hi
  have hh := noninvariant_count_three (hk3 ▸ hG) hi
  rw [hk3] at hfail
  norm_num at hfail
  linarith

universe u
/-- For the original conjecture it is enough to compare the mean only for
NON-INVARIANT critical graphs of count at least four. The supplied comparison
is still an unproved hypothesis; invariant graphs use their known linear
bound instead of any unproved fractional-exactness assertion. -/
lemma conjecture_of_high_noninvariant_mean_comparison (K : ℝ) (hK : 0 ≤ K)
    (hcomp : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      IsCountCritical k G → 4 ≤ k → ¬ InvariantPartitions.HasInvariantCount G →
      (k : ℝ) ≤ K * fractionalMean G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨4+2*K,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hcard⟩ := bound_of_critical_subgraph_bound G he
    ((4+2*K)*Fintype.card V) (by positivity) (by
      intro H _ k hk
      have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      by_cases hi : InvariantPartitions.HasInvariantCount H
      · have hb := hi.number_le_support hk.1
        rw [hk.2.1] at hb
        have hs : H.support.ncard ≤ Fintype.card V := by
          simpa using Set.ncard_le_ncard (Set.subset_univ H.support)
        have hb' : (k : ℝ) ≤ Fintype.card V := by exact_mod_cast hb.trans hs
        have hkn := mul_nonneg hK hn
        nlinarith
      · by_cases hlarge : 4 ≤ k
        · have hl := hcomp H k hk hlarge hi
          have hu := mul_le_mul_of_nonneg_left (fractionalMean_le_linear H) hK
          nlinarith
        · have hl : (k : ℝ) ≤ 2 * fractionalMean H := by
            by_cases hsmall : k ≤ 2
            · simpa only [hk.2.1] using count_le_two hk.1 (by rw [hk.2.1]; exact hsmall)
            · have hk3 : k = 3 := by omega
              simpa only [hk3,Nat.cast_ofNat] using noninvariant_count_three (hk3 ▸ hk) hi
          have hu := fractionalMean_le_linear H
          have hkn := mul_nonneg hK hn
          nlinarith)
  refine ⟨D,?_,hd,hcard⟩
  intro H hH
  apply Or.inl
  refine ⟨(hc H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc H hH).2 v




end Erdos184.LowCountMean
