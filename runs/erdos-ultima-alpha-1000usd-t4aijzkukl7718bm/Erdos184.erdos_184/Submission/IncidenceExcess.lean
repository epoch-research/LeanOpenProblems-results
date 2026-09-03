import Submission.RigidityDegree

/-! Weighted incidence counting and an edge-excess bound for rigid graphs.
No assertion about arbitrary even-minimal cores is made here. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.ChordalIncidence
set_option maxHeartbeats 2000000
variable {V I : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma no_incidenceCycle_erase (E : I → Finset V) (hno : ¬ IncidenceCycle E) (v : V) :
    ¬ IncidenceCycle (fun i => (E i).erase v) := by
  rintro ⟨a,p,hp,label,hl⟩
  have hle : primal (fun i => (E i).erase v) ≤ primal E := by
    rintro x y ⟨hxy,i,hx,hy⟩
    exact ⟨hxy,i,Finset.mem_of_mem_erase hx,Finset.mem_of_mem_erase hy⟩
  have havoid (x : V) (hx : x ∈ p.support) : x ≠ v := by
    obtain ⟨y,_,hxy⟩ := SimpleGraph.adj_of_mem_walk_support p hp.not_nil hx
    obtain ⟨_,i,hi,_⟩ := hxy
    exact (Finset.mem_erase.mp hi).1
  let q := p.mapLe hle
  have heq : q.edges = p.edges := Walk.edges_mapLe_eq_edges _ _
  let label' : {e : Sym2 V // e ∈ q.edges} → I :=
    fun e => label ⟨e.val,heq ▸ e.property⟩
  apply hno
  refine ⟨a,q,hp.mapLe hle,label',?_⟩
  intro e x hx
  have hx' : x ∈ p.support := by
    simpa only [q,Walk.support_mapLe_eq_support] using hx
  have h := hl ⟨e.val,heq ▸ e.property⟩ x hx'
  change x ∈ E (label ⟨e.val,heq ▸ e.property⟩) ↔ x ∈ e.val
  exact ⟨fun hxE => h.mp (Finset.mem_erase.mpr ⟨havoid x hx',hxE⟩),
    fun hxe => Finset.mem_of_mem_erase (h.mpr hxe)⟩

/-- For a cycle-free incidence family with pair intersections at most two,
charge each piece only for its vertices in excess of two. Small pieces cost zero. -/
lemma sum_card_sub_two_le_union [Fintype I] [DecidableEq I]
    (E : I → Finset V)
    (hinter : ∀ i j, i ≠ j → (E i ∩ E j).card ≤ 2)
    (hno : ¬ IncidenceCycle E) :
    (∑ i, ((E i).card - 2)) ≤ (Finset.univ.biUnion E).card := by
  have main : ∀ n : ℕ, ∀ E : I → Finset V,
      (Finset.univ.biUnion E).card = n →
      (∀ i j, i ≠ j → (E i ∩ E j).card ≤ 2) →
      (¬ IncidenceCycle E) →
      (∑ i, ((E i).card - 2)) ≤ (Finset.univ.biUnion E).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E hn hinter hno
      by_cases hlarge : ∃ i, 3 ≤ (E i).card
      · let A : Finset I := Finset.univ.filter (fun i => 3 ≤ (E i).card)
        have hA : A.Nonempty := by
          obtain ⟨i,hi⟩ := hlarge
          exact ⟨i,by simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]; exact hi⟩
        letI : Nonempty A := hA.to_subtype
        have hnoA := no_incidenceCycle_subfamily E hno A
        obtain ⟨v,i,hvi,hu⟩ := exists_private_vertex (fun i : A => E i.val)
          (fun i => (Finset.mem_filter.mp i.property).2)
          (fun i j hij => hinter i.val j.val (fun he => hij (Subtype.ext he)))
          (conformal_of_no_incidenceTriangle _ (fun h => hnoA (h.incidenceCycle _)))
          (primal_chordal_of_no_incidenceCycle _ hnoA).cliqueCutProperty
        have hsize : 3 ≤ (E i.val).card := (Finset.mem_filter.mp i.property).2
        have hunique (j : I) (hj : 3 ≤ (E j).card) (hvj : v ∈ E j) : j = i.val := by
          have hjA : j ∈ A := by simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]; exact hj
          exact congrArg Subtype.val (hu ⟨j,hjA⟩ hvj)
        let E' : I → Finset V := fun j => (E j).erase v
        have hinter' (j k : I) (hjk : j ≠ k) : (E' j ∩ E' k).card ≤ 2 := by
          apply (Finset.card_le_card ?_).trans (hinter j k hjk)
          intro x hx
          exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hx).1,
            Finset.mem_of_mem_erase (Finset.mem_inter.mp hx).2⟩
        have hU : Finset.univ.biUnion E' = (Finset.univ.biUnion E).erase v := by
          ext x
          simp only [E',Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_erase]
          aesop
        have hvU : v ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨i.val,Finset.mem_univ _,hvi⟩
        have hlt : (Finset.univ.biUnion E').card < n := by
          rw [hU]
          exact (Finset.card_erase_lt_of_mem hvU).trans_eq hn
        have hb := ih _ hlt E' rfl hinter' (no_incidenceCycle_erase E hno v)
        have hcost (j : I) : (E j).card - 2 = (E' j).card - 2 + if j = i.val then 1 else 0 := by
          by_cases hji : j = i.val
          · subst j
            have hc := Finset.card_erase_add_one hvi
            dsimp only [E']
            rw [if_pos rfl]
            omega
          · rw [if_neg hji,add_zero]
            by_cases hj : 3 ≤ (E j).card
            · have hvj : v ∉ E j := fun hvj => hji (hunique j hj hvj)
              simp only [E',Finset.erase_eq_of_notMem hvj]
            · have hle : (E' j).card ≤ (E j).card := Finset.card_le_card (Finset.erase_subset _ _)
              omega
        have hsum : (∑ j, ((E j).card - 2)) = (∑ j, ((E' j).card - 2)) + 1 := by
          calc
            _ = ∑ j, ((E' j).card - 2 + if j = i.val then 1 else 0) :=
              Finset.sum_congr rfl (fun j _ => hcost j)
            _ = _ := by rw [Finset.sum_add_distrib]; simp
        have hcard := Finset.card_erase_add_one hvU
        rw [← hU] at hcard
        omega
      · have hz (i : I) : (E i).card - 2 = 0 := by
          have hi : ¬ 3 ≤ (E i).card := fun hi => hlarge ⟨i,hi⟩
          omega
        simp only [hz,Finset.sum_const_zero,Nat.zero_le]
  exact main _ E rfl hinter hno

/-- The weighted incidence inequality counts edges of a cycle family. -/
lemma cycle_family_edge_excess {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hinter : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).ncard ≤ 2)
    (hno : ¬ IncidenceCycle (pieceVertices D)) :
    (subfamilyGraph D).edgeFinset.card ≤ G.support.ncard + 2 * D.card := by
  have hsize (H : D) : 3 ≤ (pieceVertices D H).card := by
    obtain ⟨v⟩ := (hD H.val H.property).1.nonempty
    have hd := H.val.coe.degree_lt_card_verts v
    have hr := (hD H.val H.property).2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hr
    simp only [pieceVertices,Set.toFinset_card,← Nat.card_eq_fintype_card]
    omega
  have hpair (H K : D) (hne : H ≠ K) :
      (pieceVertices D H ∩ pieceVertices D K).card ≤ 2 := by
    have hp := hinter H.val H.property K.val K.property (fun h => hne (Subtype.ext h))
    simpa only [pieceVertices,← Set.toFinset_inter,Set.toFinset_card,← Nat.card_eq_fintype_card] using hp
  have hweighted := sum_card_sub_two_le_union (pieceVertices D) hpair hno
  have hsub : Finset.univ.biUnion (pieceVertices D) ⊆ G.support.toFinset := by
    intro x hx
    obtain ⟨H,_,hxH⟩ := Finset.mem_biUnion.mp hx
    have hxH : x ∈ H.val.verts := Set.mem_toFinset.mp hxH
    let v : H.val.verts := ⟨x,hxH⟩
    have hr := (hD H.val H.property).2 v
    have hpos : 0 < H.val.coe.degree v := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr ⊢
      omega
    obtain ⟨y,hxy⟩ := (H.val.coe.degree_pos_iff_exists_adj v).mp hpos
    exact Set.mem_toFinset.mpr ⟨y.val,H.val.adj_sub hxy⟩
  have hsupport := Finset.card_le_card hsub
  simp only [Set.toFinset_card,← Nat.card_eq_fintype_card] at hsupport
  change (Finset.univ.biUnion (pieceVertices D)).card ≤ G.support.ncard at hsupport
  have hsum : (∑ H : D, (pieceVertices D H).card) =
      (∑ H : D, ((pieceVertices D H).card - 2)) + 2 * D.card := by
    calc
      _ = ∑ H : D, ((pieceVertices D H).card - 2 + 2) := by
        apply Finset.sum_congr rfl
        intro H _
        have hs := hsize H
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  have hedges : (subfamilyGraph D).edgeFinset.card = ∑ H : D, (pieceVertices D H).card := by
    rw [subfamilyGraph_card_edges D hd,← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro H _
    have he := MaximumCycles.regular_two_card_edges H.val (by
      simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hD H.val H.property).2)
    rw [subgraph_edge_card] at he
    change H.val.coe.edgeFinset.card = Nat.card H.val.verts at he
    simpa only [pieceVertices,Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using he
  omega

/-- Rigid even graphs satisfy the edge-excess estimate with coefficient one.
The corresponding estimate for arbitrary minimal cores is not asserted. -/
lemma rigid_edge_excess {G : SimpleGraph V} (hrig : Rigidity.CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) :
    G.edgeFinset.card ≤ G.support.ncard + 2 * Critical.number G := by
  obtain ⟨D,hD,hdec,hcard⟩ := Rigidity.minimum_cycles heven
  have hb := cycle_family_edge_excess D hD hdec.1
    (fun H hH K hK hne => RigidSwitching.rigid_pair_intersection_le_two hrig heven H K
      (hD H hH) (hD K hK) (hdec.1 hH hK hne))
    (CycleRings.no_incidenceCycle hrig heven D hD hdec.1)
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  rw [hg,hcard] at hb
  exact hb

#print axioms no_incidenceCycle_erase
#print axioms sum_card_sub_two_le_union
#print axioms cycle_family_edge_excess
#print axioms rigid_edge_excess
end Erdos184Work.ChordalIncidence
