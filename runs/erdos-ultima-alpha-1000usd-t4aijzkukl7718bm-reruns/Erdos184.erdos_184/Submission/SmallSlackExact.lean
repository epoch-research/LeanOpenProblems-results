import Submission.FractionalEnvelope
import Submission.StarElimination
import Submission.OneVertexCycles

/-! Fractional exactness for a star of cycles and for packings of at most two
cycles. The resulting small-slack split is restricted, not a general splitting
or rounding theorem. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.SmallSlackExact
open FractionalCycles FractionalEnvelope StarElimination
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

lemma union_even (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet)) :
    ∀ v, Even ((unionPieces G S).degree v) := by
  intro v
  rw [unionPieces_degree G S hd v]
  exact Finset.even_sum _ (fun H hH => regular_two_piece_degree_even H (hc H hH).2 v)

noncomputable def unionCycle (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (i : {H // H ∈ S}) : CyclePiece (unionPieces G S) :=
  ⟨{ verts := i.val.verts
     Adj := i.val.Adj
     adj_sub := by
       intro a b hab
       change s(a,b) ∈ (unionPieces G S).edgeSet
       rw [unionPieces_edgeSet]
       exact Set.mem_iUnion₂.mpr ⟨i.val,i.property,hab⟩
     symm := i.val.symm
     edge_vert := i.val.edge_vert },
    (hc i.val i.property).1, by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hc i.val i.property).2 v⟩

lemma optimum_le_card (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet)) :
    optimum (unionPieces G S) ≤ (S.card : ℝ) := by
  let C := unionCycle S hc
  have hf : IsFractionalPartition (unionPieces G S) (pushWeight C (fun _ => 1)) := by
    apply fractional_of_family _ C _ (by intro i; norm_num)
    intro e he
    rw [unionPieces_edgeSet] at he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    let i : {H // H ∈ S} := ⟨H,hH⟩
    rw [Finset.sum_eq_single i]
    · change (if e ∈ H.edgeSet then (1 : ℝ) else 0) = 1
      simp [heH]
    · intro j _ hji
      change (if e ∈ j.val.edgeSet then (1 : ℝ) else 0) = 0
      apply if_neg
      intro hej
      exact Set.disjoint_left.mp (hd j.property hH (fun h => hji (Subtype.ext h))) hej heH
    · simp
  have hh := optimum_le_cost hf
  simpa only [cost,pushWeight_sum,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul,mul_one] using hh

lemma star_exact (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet))
    (v : V) (hv : ∀ H ∈ S, v ∈ H.verts) :
    optimum (unionPieces G S) = (S.card : ℝ) := by
  apply le_antisymm (optimum_le_card S hc hd)
  have he := union_even S hc hd
  have hl := degree_le_twice_optimum (unionPieces G S) (by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he w) v
  have hdeg : (unionPieces G S).degree v = 2 * S.card := by
    rw [unionPieces_degree G S hd v]
    have hh : ∀ H ∈ S, H.degree v = 2 := by
      intro H hH
      simpa only [cycle_piece_degree,if_pos (hv H hH)] using
        (cycle_piece_degree G ⟨H,hc H hH⟩ v)
    rw [Finset.sum_congr rfl hh]
    simp [Nat.mul_comm]
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hl
  rw [hdeg] at hl
  norm_num at hl
  linarith

lemma two_edges_lower (A : SimpleGraph V) (t : CyclePiece A → ℝ)
    (ht : IsFractionalPartition A t) (e f : Sym2 V)
    (he : e ∈ A.edgeSet) (hf : f ∈ A.edgeSet)
    (hsep : ∀ H : CyclePiece A, ¬(e ∈ H.val.edgeSet ∧ f ∈ H.val.edgeSet)) :
    2 ≤ cost t := by
  have hbound : (∑ H : CyclePiece A, if e ∈ H.val.edgeSet then t H else 0) +
      (∑ H : CyclePiece A, if f ∈ H.val.edgeSet then t H else 0) ≤ cost t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro H _
    by_cases heH : e ∈ H.val.edgeSet <;> by_cases hfH : f ∈ H.val.edgeSet
    · exact (hsep H ⟨heH,hfH⟩).elim
    · simp [heH,hfH]
    · simp [heH,hfH]
    · simpa [heH,hfH] using ht.1 H
  rw [ht.2 e he,ht.2 f hf] at hbound
  norm_num at hbound ⊢
  exact hbound

lemma pair_exact (H K : G.Subgraph) (hne : H ≠ K)
    (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) :
    optimum (unionPieces G {H,K}) = 2 := by
  have hc : ∀ J ∈ ({H,K} : Finset G.Subgraph),
      J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
    intro J hJ
    rcases (show J = H ∨ J = K by simpa using hJ) with rfl | rfl
    · exact hcH
    · exact hcK
  have hdis : Set.PairwiseDisjoint (({H,K} : Finset G.Subgraph) : Set G.Subgraph)
      (fun J => J.edgeSet) := by
    intro J hJ L hL hJL
    have hJ' : J = H ∨ J = K := by simpa using hJ
    have hL' : L = H ∨ L = K := by simpa using hL
    rcases hJ' with rfl | rfl <;> rcases hL' with rfl | rfl
    · exact (hJL rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hJL rfl).elim
  by_cases hv : ∃ v, v ∈ H.verts ∧ v ∈ K.verts
  · obtain ⟨v,hvH,hvK⟩ := hv
    have hh := star_exact {H,K} hc hdis v (by
      intro J hJ
      rcases (show J = H ∨ J = K by simpa using hJ) with rfl | rfl <;> assumption)
    simpa only [Finset.card_pair hne,Nat.cast_ofNat] using hh
  let A := unionPieces G {H,K}
  have hcover : H.spanningCoe.edgeSet ∪ K.spanningCoe.edgeSet = A.edgeSet := by
    change H.edgeSet ∪ K.edgeSet = (unionPieces G {H,K}).edgeSet
    rw [unionPieces_edgeSet]
    ext e
    simp
  have hover : (H.spanningCoe.support ∩ K.spanningCoe.support).ncard ≤ 1 := by
    have hz : H.spanningCoe.support ∩ K.spanningCoe.support = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨w,hw⟩,⟨z,hz⟩⟩
      exact hv ⟨v,H.edge_vert hw,K.edge_vert hz⟩
    simp [hz]
  obtain ⟨e,he⟩ := cycle_edgeSet_nonempty H hcH.1 hcH.2
  obtain ⟨f,hf⟩ := cycle_edgeSet_nonempty K hcK.1 hcK.2
  have heA : e ∈ A.edgeSet := hcover ▸ (show e ∈ H.spanningCoe.edgeSet ∪ K.spanningCoe.edgeSet from Or.inl he)
  have hfA : f ∈ A.edgeSet := hcover ▸ (show f ∈ H.spanningCoe.edgeSet ∪ K.spanningCoe.edgeSet from Or.inr hf)
  apply le_antisymm
  · simpa only [Finset.card_pair hne,Nat.cast_ofNat] using optimum_le_card {H,K} hc hdis
  · obtain ⟨t,ht,hcost⟩ := optimum_attained A (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using union_even {H,K} hc hdis v)
    rw [← hcost]
    apply two_edges_lower A t ht e f heA hfA
    intro J ⟨heJ,hfJ⟩
    rcases cycle_contained_in_one_vertex_separation hcover hover J.val
      J.property.1 J.property.2 with hJ | hJ
    · exact Set.disjoint_left.mp hd (hJ hfJ) hf
    · exact Set.disjoint_left.mp hd he (hJ heJ)

lemma at_most_two_exact (S : Finset G.Subgraph)
    (hc : ∀ H ∈ S, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet))
    (hcard : S.card ≤ 2) : optimum (unionPieces G S) = (S.card : ℝ) := by
  interval_cases hn : S.card
  · have hS := Finset.card_eq_zero.mp hn
    subst S
    simpa only [unionPieces,Finset.sup_empty,Subgraph.spanningCoe_bot,Finset.card_empty,
      Nat.cast_zero] using (optimum_bot (V := V))
  · obtain ⟨H,rfl⟩ := Finset.card_eq_one.mp hn
    obtain ⟨v,hv⟩ := (hc H (by simp)).1.nonempty
    exact star_exact {H} hc hd v (by simpa using hv)
  · obtain ⟨H,K,hne,rfl⟩ := Finset.card_eq_two.mp hn
    simpa only [Finset.card_pair hne,Nat.cast_ofNat] using
      pair_exact H K hne (hc H (by simp)) (hc K (by simp)) (hd (by simp) (by simp) hne)

/-- Any cycle partition with at most two pieces avoiding a vertex splits
into its star and a complementary fractionally exact family. No assertion
that such a vertex exists in every graph is made. -/
lemma split_of_small_slack (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V)
    (hslack : 2 * D.card ≤ G.degree v + 4) :
    optimum (unionPieces G (star D v)) = ((star D v).card : ℝ) ∧
    optimum (unionPieces G (D \ star D v)) = ((D \ star D v).card : ℝ) := by
  have hs := star_subset D v
  have hcS : ∀ H ∈ star D v, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (hs hH)
  have hdS : Set.PairwiseDisjoint ((star D v : Finset G.Subgraph) : Set G.Subgraph)
      (fun H => H.edgeSet) := fun _ hH _ hK hne => hd.1 (hs hH) (hs hK) hne
  refine ⟨star_exact (star D v) hcS hdS v (fun H hH => ((mem_star D v H).mp hH).2),?_⟩
  apply at_most_two_exact
  · intro H hH
    exact hc H (Finset.mem_sdiff.mp hH).1
  · intro H hH K hK hne
    exact hd.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
  · have hdeg := star_card D hc hd v
    have hcard := Finset.card_sdiff_add_card_eq_card hs
    omega

end Erdos184.SmallSlackExact
