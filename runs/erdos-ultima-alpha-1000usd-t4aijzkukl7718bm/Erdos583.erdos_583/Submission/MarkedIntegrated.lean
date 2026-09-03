import Submission.AnchorIntegrated

/-! Integrated development layer for marked edge absorption. -/
namespace Erdos583Work

/- Edge absorption by marked outside groups at or below their even budget. -/
namespace MarkedAbsorption
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.QuotaSurgery
open _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.MarkedCycleGroups _root_.Erdos583Work.VertexCritical _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.EdgeAbsorption _root_.Erdos583Work.CarrierCount _root_.Erdos583Work.CarrierLength
open _root_.Erdos583Work.CarrierGroups _root_.Erdos583Work.OutsideCarrierBudget _root_.Erdos583Work.AnchorCarrier
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma append_edge_at_mark [Fintype V] (H : SimpleGraph V) {w x : V}
    (hwx : w ≠ x) (hx : x ∉ H.support) (t : ℕ) (hm : MarkedPartition H t w) :
    ∃ D : Finset (H ⊔ edge w x).Subgraph,
      GoodDecomposition (H ⊔ edge w x) D ∧ D.card ≤ t := by
  obtain ⟨D,b,P,hD,hDc,hP,_,hPD⟩ := hm
  have hedge : (H ⊔ edge w x).Adj x w :=
    Or.inr ((edge_adj w x x w).mpr ⟨Or.inr ⟨rfl,rfl⟩,hwx.symm⟩)
  obtain ⟨E,hE,hEc⟩ := MarkedBudgets.append_marked_to_isolated le_sup_left hedge
    (fun y hxy ↦ hx ⟨y,hxy⟩)
    (by rw [edgeSet_sup,edge_edgeSet_of_ne hwx,Sym2.eq_swap]; ext d; simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]; tauto)
    D hD P hP hPD
  exact ⟨E,hE,hDc ▸ hEc⟩

lemma marked_edge_partition {n t : ℕ} (hsmall : SmallerOrders n)
    [Fintype V] (H : SimpleGraph V) (hc : SupportConnected H)
    {w x : V} (hwx : w ≠ x) (hw : w ∈ H.support)
    (horder : H.support.ncard < n) (hsize : H.support.ncard ≤ 2*t)
    (hm : MarkedPartition H t w) :
    ∃ D : Finset (H ⊔ edge w x).Subgraph,
      GoodDecomposition (H ⊔ edge w x) D ∧ D.card ≤ t := by
  classical
  by_cases hx : x ∈ H.support
  · have hsub : (H ⊔ edge w x).support ⊆ H.support := by
      intro z hz
      rcases attach_edge_support H hw hz with hzx|hz
      · exact hzx ▸ hx
      · exact hz
    have hb := Set.ncard_le_ncard hsub
    obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall
      (H ⊔ edge w x) (attach_edge_connected H hc hw) (by omega)
    rw [ceil_half] at hDc
    exact ⟨D,hD,by omega⟩
  · exact append_edge_at_mark H hwx hx t hm

lemma suffix_nonempty_of_absorption [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (hi : ¬(T.walk i).IsPath)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    {w x b : V} (h : G.Adj w x) (q : G.Walk x b)
    (hj : (T.walk j).toSubgraph=(Walk.cons h q).toSubgraph)
    (D : Finset (selectedGraph T F ⊔ edge w x).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge w x) D) (hDc : D.card ≤ F.card) : ¬q.Nil := by
  classical
  intro hn
  cases q with
  | nil =>
    have he : selectedGraph T (insert j F)=selectedGraph T F ⊔ edge w x := by
      ext u v
      change (∃ l ∈ insert j F, (T.walk l).toSubgraph.Adj u v) ↔
        (∃ l ∈ F, (T.walk l).toSubgraph.Adj u v) ∨ (edge w x).Adj u v
      simp only [Finset.mem_insert,or_and_right,exists_or,exists_eq_left,hj,
        Walk.toSubgraph_cons_nil_eq_subgraphOfAdj,subgraphOfAdj_adj,edge_adj]
      have hwx := h.ne
      aesop (add safe hwx)
    have hex : ∃ E : Finset (selectedGraph T (insert j F)).Subgraph,
        GoodDecomposition (selectedGraph T (insert j F)) E ∧ E.card ≤ F.card := by
      rw [he]
      exact ⟨D,hD,hDc⟩
    obtain ⟨E,hE,hEc⟩ := hex
    have hb := normal_group_cannot_save hfail T hs i hi (insert j F)
      (by simp [hiF,hij]) E hE
    rw [Finset.card_insert_of_notMem hjF] at hb
    omega
  | cons hq q => simp at hn
lemma no_absorbable_carrier_start [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j)
    (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ z ∈ (selectedGraph T F).support, z ∉ K.verts)
    {w x b : V} (h : G.Adj w x) (q : G.Walk x b)
    (hp : (Walk.cons h q).IsPath) (hj : (T.walk j).toSubgraph=(Walk.cons h q).toSubgraph)
    (hw : w ∈ (selectedGraph T F).support)
    (hcarrier : Touches K.verts (T.walk j).toSubgraph)
    (D : Finset (selectedGraph T F ⊔ edge w x).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge w x) D) (hDc : D.card ≤ F.card) : False := by
  classical
  have hnp := member_not_path T i K hnK hi
  have hqn := suffix_nonempty_of_absorption hfail T hs i j hij hnp F hiF hjF h q hj D hD hDc
  have hqC : Touches K.verts q.toSubgraph := by
    obtain ⟨z,hz,y,hzy⟩ := hcarrier
    have hzw : z ≠ w := fun hh ↦ hFC w hw (hh ▸ hz)
    have hzq : z ∈ q.support := by
      have hh := Walk.mem_support_of_adj_toSubgraph hzy
      rw [←Walk.mem_verts_toSubgraph,hj,Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons] at hh
      exact hh.resolve_left hzw
    exact touches_of_nonempty_inter q hp.of_cons hqn ⟨z,hz,q.mem_verts_toSubgraph.mpr hzq⟩
  obtain ⟨U,hUs,hUj,hrest,hUF,hcov⟩ := absorb_first_edge hfail T hs i j hij hnp F hiF hjF
    h q hp hqn hj D hD hDc
  have hUi : (U.walk i).toSubgraph=K := (hrest i hiF hij).trans hi
  have hUjC : Touches K.verts (U.walk j).toSubgraph := hUj.symm ▸ hqC
  have hTF (l) (hl : l ∈ F) : ¬Touches K.verts (T.walk l).toSubgraph := by
    rintro ⟨z,hz,y,hzy⟩
    exact hFC z ⟨y,l,hl,hzy⟩ hz
  by_cases hx : x ∈ K.verts
  · have hedge : s(w,x) ∈ (selectedGraph T F ⊔ edge w x).edgeSet := by
      exact Or.inr ((edge_adj w x w x).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.ne⟩)
    obtain ⟨m,hmF,hmE⟩ := hcov _ hedge
    have hmU : Touches K.verts (U.walk m).toSubgraph :=
      ⟨x,hx,w,Subgraph.Adj.symm hmE⟩
    have hlt := FreeCarrier.carrierCount_strict_of_new T U K.verts m (hTF m hmF) hmU (by
      intro l hl
      by_cases hlj : l=j
      · subst l; exact hUjC
      have hlF : l ∉ F := fun hh ↦ hTF l hh hl
      rw [hrest l hlF hlj]
      exact hl)
    have hle := hmax U hUs hUi
    omega
  · have hnoUF (l) (hl : l ∈ F) : ¬Touches K.verts (U.walk l).toSubgraph := by
      rintro ⟨z,hz,y,hzy⟩
      have hzyJ : s(z,y) ∈ (selectedGraph T F ⊔ edge w x).edgeSet := hUF l hl hzy
      have hzJ : z ∈ (selectedGraph T F ⊔ edge w x).support := ⟨y,hzyJ⟩
      rcases attach_edge_support (selectedGraph T F) hw hzJ with hzx|hzF
      · exact hx (hzx ▸ hz)
      · exact hFC z hzF hz
    have hUc : carrierCount U K.verts=carrierCount T K.verts := by
      apply carrierCount_congr
      intro l
      by_cases hlj : l=j
      · subst l; exact iff_of_true hUjC hcarrier
      by_cases hlF : l ∈ F
      · exact iff_of_false (hnoUF l hlF) (hTF l hlF)
      · rw [hrest l hlF hlj]
    have hUl : carrierLength U K.verts+1=carrierLength T K.verts := by
      apply carrierLength_change_one T U K.verts j 1
      · simp only [if_pos hUjC,if_pos hcarrier]
        rw [trail_length_of_same_subgraph _ _ (U.isTrail j) hp.of_cons.isTrail hUj,
          trail_length_of_same_subgraph _ _ (T.isTrail j) hp.isTrail hj,Walk.length_cons]
      · intro l hlj
        by_cases hlF : l ∈ F
        · simp only [if_neg (hnoUF l hlF),if_neg (hTF l hlF)]
        · exact carrier_weight_of_same_subgraph T U K.verts l (hrest l hlF hlj)
    have hle := hmin U hUs hUi hUc
    omega


lemma fully_marked_small_group_avoids_carriers {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ z ∈ (selectedGraph T F).support, z ∉ K.verts)
    (hconn : SupportConnected (selectedGraph T F))
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hmark : ∀ z ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card z)
    (hcarrier : Touches K.verts (T.walk j).toSubgraph) :
    ∀ z ∈ (T.walk j).support, z ∉ (selectedGraph T F).support := by
  intro z hz hzF
  have hnp := member_not_path T i K hnK hi
  have hpj := (T.one_defect_other_paths hs i hnp).2 j hij.symm
  have hFcard : F.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ F,fun hh ↦ hiF (hh.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  have horder : (selectedGraph T F).support.ncard < n := by
    simp only [Fintype.card_fin,ceil_half] at hFcard
    omega
  have hend := fully_marked_group_contains_carrier_endpoint T hs i j hij K hnK hi
    (fun U hUs hUi _ ↦ hmax U hUs hUi)
    (fun U hUs hUi _ hUc ↦ hmin U hUs hUi hUc)
    F hiF hjF hFC hmark hcarrier ⟨z,hz,hzF⟩
  have hno (w b : Fin n) (P : G.Walk w b) (hP : P.IsPath)
      (hj : (T.walk j).toSubgraph=P.toSubgraph) : w ∉ (selectedGraph T F).support := by
    intro hw
    cases P with
    | nil =>
      rw [hj] at hcarrier
      simp [Touches] at hcarrier
    | @cons w x b h q =>
      obtain ⟨D,hD,hDc⟩ := marked_edge_partition hsmall (selectedGraph T F) hconn h.ne hw horder hsize (hmark w hw)
      exact no_absorbable_carrier_start hfail T hs i j hij K hnK hi hmax hmin
        F hiF hjF hFC h q hP hj hw hcarrier D hD hDc
  rcases hend with hstart|hfinish
  · exact hno _ _ (T.walk j) hpj rfl hstart
  · exact hno _ _ (T.walk j).reverse hpj.reverse (by rw [Walk.toSubgraph_reverse]) hfinish


lemma unmarked_normal_group_even [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (F : Finset (Fin k)) (hiF : i ∉ F)
    (x : V) (hno : ¬MarkedPartition (selectedGraph T F) F.card x) :
    Even (Nat.card ((selectedGraph T F).neighborSet x)) := by
  classical
  by_contra hn
  have hx : Odd ((selectedGraph T F).degree x) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using Nat.not_even_iff_odd.mp hn
  obtain ⟨D,hD,hDc,hne⟩ := normal_group_exact hfail T hs i hi F hiF
  have hpos := ((hD.odd_endpointMultiplicity_iff x).mpr hx).pos
  obtain ⟨b,P,hP,hPD⟩ := MarkedBudgets.marked_of_positive_endpoint hD hpos
  apply hno
  refine ⟨D,b,P,hD,hDc,hP,?_,hPD⟩
  intro hnP
  obtain ⟨e,he⟩ := hne P.toSubgraph hPD
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hnP,List.not_mem_nil] at he

lemma unmarked_normal_group_many_even [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (F : Finset (Fin k)) (hiF : i ∉ F)
    (hc : SupportConnected (selectedGraph T F)) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (x : V) (hx : x ∈ (selectedGraph T F).support)
    (hno : ¬MarkedPartition (selectedGraph T F) F.card x) :
    4 ≤ (Finset.univ.filter fun v : (selectedGraph T F).support ↦
      Even (((selectedGraph T F).induce (selectedGraph T F).support).degree v)).card := by
  classical
  let J := selectedGraph T F
  have hcard : Fintype.card J.support=J.support.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨y,hy⟩ := (show ∃ y, J.Adj x y from hx)
  letI : Nontrivial J.support := ⟨⟨⟨x,hx⟩,⟨y,⟨x,hy.symm⟩⟩,
    fun hh ↦ hy.ne (congrArg Subtype.val hh)⟩⟩
  by_contra hn
  have hfew : (Finset.univ.filter fun v : J.support ↦ Even ((J.induce J.support).degree v)).card ≤ 3 := by
    convert (show (Finset.univ.filter fun v : (selectedGraph T F).support ↦
      Even (((selectedGraph T F).induce (selectedGraph T F).support).degree v)).card ≤ 3 from by omega) using 1
  obtain ⟨D,b,P,hD,hP,hPD,hDc⟩ := MarkedBudgets.few_even_marked (J.induce J.support)
    (hc.induce_support ⟨x,hx⟩) ⟨x,hx⟩ hfew
  apply hno
  apply normal_group_marked_of_support hfail T hs i hi F hiF hx
  refine ⟨D,hD,?_,b,P,hP,hPD⟩
  rw [hcard,ceil_half] at hDc
  change J.support.ncard ≤ 2*F.card at hsize
  omega

lemma unmarked_normal_group_large {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (F : Finset (Fin k)) (hiF : i ∉ F)
    (hc : SupportConnected (selectedGraph T F)) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (x : Fin n) (hx : x ∈ (selectedGraph T F).support)
    (hno : ¬MarkedPartition (selectedGraph T F) F.card x) :
    n ≤ 2*(selectedGraph T F).support.ncard := by
  by_contra hn
  exact hno (small_normal_group_marked hsmall hfail T hs i hi F hiF hc (by omega) hsize x hx)

lemma degree_lt_support [Fintype V] (H : SimpleGraph V) (x : V) (hx : x ∈ H.support) :
    Nat.card (H.neighborSet x) < H.support.ncard := by
  have hsub : H.neighborSet x ⊆ H.support := fun y hy ↦ ⟨x,hy.symm⟩
  have hproper : H.neighborSet x ⊂ H.support := Set.ssubset_iff_subset_ne.mpr ⟨hsub,by
    intro he
    have hh : x ∈ H.neighborSet x := he.symm ▸ hx
    exact hh.ne rfl⟩
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_lt_ncard hproper

lemma zero_outside_component_unmarked {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (D : (GroupComponents.inducedGraph T (outsideIndices T K.verts)).ConnectedComponent)
    (hzero : (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support.ncard =
      2*(GroupComponents.componentMembers T (outsideIndices T K.verts) D).card) :
    ∃ x ∈ (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support,
      ¬MarkedPartition (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D))
        (GroupComponents.componentMembers T (outsideIndices T K.verts) D).card x := by
  classical
  let B := outsideIndices T K.verts
  have hiB : i ∉ B := fun hh ↦ outside_not_touched T K.verts hh (anchor_touches T i K hnK hi)
  have hnp := member_not_path T i K hnK hi
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩
  let F := GroupComponents.componentMembers T B D
  have hFB : F ⊆ B := GroupComponents.componentMembers_subset T B D
  have hFC (z : Fin n) (hz : z ∈ (selectedGraph T F).support) : z ∉ K.verts := by
    intro hzC
    exact outside_support_avoids T K.verts
      (SimpleGraph.support_mono (CycleGroupDisjoint.selectedGraph_mono T hFB) hz)
      (hzC)
  obtain ⟨j,hj,x,hxj,hxF⟩ := GroupComponents.component_meets_outside T hG B ⟨i,hiB⟩ hn D
  have hcarrier : Touches K.verts (T.walk j).toSubgraph := by
    by_contra hh
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  have hji : j ≠ i := by
    rintro rfl
    exact hFC x hxF (by rwa [←Walk.mem_verts_toSubgraph,hi] at hxj)
  by_contra! hmark
  exact fully_marked_small_group_avoids_carriers hsmall hfail T hs i j hji.symm K hnK hi hmax hmin F
    (fun hh ↦ hiB (hFB hh)) (fun hh ↦ hj (hFB hh)) hFC
    (GroupComponents.component_support_connected T B D) hzero.le hmark hcarrier x hxj hxF

lemma zero_outside_component_structure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (D : (GroupComponents.inducedGraph T (outsideIndices T K.verts)).ConnectedComponent)
    (hzero : (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support.ncard =
      2*(GroupComponents.componentMembers T (outsideIndices T K.verts) D).card) :
    n ≤ 2*(selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support.ncard ∧
    4 ≤ (Finset.univ.filter fun v : (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support ↦
      Even (((selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).induce
        (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support).degree v)).card ∧
    ∃ x ∈ (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support,
      ¬MarkedPartition (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D))
        (GroupComponents.componentMembers T (outsideIndices T K.verts) D).card x ∧
      Even (Nat.card ((selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).neighborSet x)) ∧
      Nat.card ((selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).neighborSet x) <
        2*(GroupComponents.componentMembers T (outsideIndices T K.verts) D).card := by
  classical
  let B := outsideIndices T K.verts
  let F := GroupComponents.componentMembers T B D
  obtain ⟨x,hx,hno⟩ := zero_outside_component_unmarked hsmall hG hfail T hs i K hnK hi hmax hmin D hzero
  have hiF : i ∉ F := by
    intro hh
    exact outside_not_touched T K.verts (GroupComponents.componentMembers_subset T B D hh)
      (anchor_touches T i K hnK hi)
  have hnp := member_not_path T i K hnK hi
  have hconn := GroupComponents.component_support_connected T B D
  refine ⟨unmarked_normal_group_large hsmall hfail T hs i hnp F hiF hconn hzero.le x hx hno,
    unmarked_normal_group_many_even hfail T hs i hnp F hiF hconn hzero.le x hx hno,
    x,hx,hno,unmarked_normal_group_even hfail T hs i hnp F hiF x hno,?_⟩
  have hd := degree_lt_support (selectedGraph T F) x hx
  rwa [hzero] at hd

lemma zero_outside_components_unique {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (D E : (GroupComponents.inducedGraph T (outsideIndices T K.verts)).ConnectedComponent)
    (hD : (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support.ncard =
      2*(GroupComponents.componentMembers T (outsideIndices T K.verts) D).card)
    (hE : (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) E)).support.ncard =
      2*(GroupComponents.componentMembers T (outsideIndices T K.verts) E).card) : D=E := by
  classical
  by_contra hne
  let B := outsideIndices T K.verts
  let F := GroupComponents.componentMembers T B D
  let Q := GroupComponents.componentMembers T B E
  have hDlarge := (zero_outside_component_structure hsmall hG hfail T hs i K hnK hi hmax hmin D hD).1
  have hElarge := (zero_outside_component_structure hsmall hG hfail T hs i K hnK hi hmax hmin E hE).1
  have hsub : (selectedGraph T F).support ∪ (selectedGraph T Q).support ⊆ (selectedGraph T B).support := by
    apply Set.union_subset
    · exact SimpleGraph.support_mono (CycleGroupDisjoint.selectedGraph_mono T (GroupComponents.componentMembers_subset T B D))
    · exact SimpleGraph.support_mono (CycleGroupDisjoint.selectedGraph_mono T (GroupComponents.componentMembers_subset T B E))
  have hu := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq (GroupComponents.component_support_disjoint T B hne)] at hu
  change (selectedGraph T F).support.ncard+(selectedGraph T Q).support.ncard ≤ (selectedGraph T B).support.ncard at hu
  have hb := outside_support_anchor_card T K
  simp only [Fintype.card_fin] at hb
  obtain ⟨x,hx,_,_⟩ := anchor_touches T i K hnK hi
  have hkpos : 0 < K.verts.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨x,hx⟩
  change (selectedGraph T B).support.ncard+K.verts.ncard ≤ n at hb
  change n ≤ 2*(selectedGraph T F).support.ncard at hDlarge
  change n ≤ 2*(selectedGraph T Q).support.ncard at hElarge
  omega

lemma half_order_zero_component_edge_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts ≤ carrierCount T K.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=K →
      carrierCount U K.verts=carrierCount T K.verts →
      carrierLength T K.verts ≤ carrierLength U K.verts)
    (D : (GroupComponents.inducedGraph T (outsideIndices T K.verts)).ConnectedComponent)
    (hzero : (selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support.ncard =
      2*(GroupComponents.componentMembers T (outsideIndices T K.verts) D).card)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hhalf : 2*(selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).support.ncard=n) :
    G.edgeSet.ncard ≤ 2*(selectedGraph T (GroupComponents.componentMembers T (outsideIndices T K.verts) D)).edgeSet.ncard+1 := by
  let B := outsideIndices T K.verts
  let F := GroupComponents.componentMembers T B D
  obtain ⟨x,hx,hno⟩ := zero_outside_component_unmarked hsmall hG hfail T hs i K hnK hi hmax hmin D hzero
  have hiF : i ∉ F := by
    intro hh
    exact outside_not_touched T K.verts (GroupComponents.componentMembers_subset T B D hh)
      (anchor_touches T i K hnK hi)
  by_contra hn
  change ¬G.edgeSet.ncard ≤ 2*(selectedGraph T F).edgeSet.ncard+1 at hn
  exact hno (half_normal_group_marked hcritical hfail T hs i (member_not_path T i K hnK hi) F hiF
    (GroupComponents.component_support_connected T B D) hhalf (by omega) hzero.le x hx)

end MarkedAbsorption

end Erdos583Work
