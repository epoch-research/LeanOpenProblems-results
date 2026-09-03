import Submission.MemberNormalExpansion

/-! Tracked replacement of whole path groups. The unchanged members retain
both endpoints and their full subgraphs, not just their edge sets. -/
namespace Erdos583GroupActivationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583MemberExpansionDevelopment Erdos583MemberNormalExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma replace_path_group_tracked (T : TrailFamily G k) (A : Finset (Fin k))
    (hpA : ∀ i ∈ A, (T.walk i).IsPath)
    (D : Finset (selectedGraph T A).Subgraph)
    (hD : GoodDecomposition (selectedGraph T A) D) (hcard : D.card=A.card) :
    ∃ U : TrailFamily G k, U.score=T.score ∧
      (∀ i, i ∉ A → U.start i=T.start i ∧ U.finish i=T.finish i ∧
        (U.walk i).toSubgraph=(T.walk i).toSubgraph) ∧
      (∀ i ∈ A, (U.walk i).IsPath) ∧
      (∀ i ∈ A, ∃ K ∈ D, (U.walk i).toSubgraph=K.map (Hom.ofLE (selectedGraph_le T A))) ∧
      ∀ K ∈ D, ∃ i ∈ A, (U.walk i).toSubgraph=K.map (Hom.ofLE (selectedGraph_le T A)) := by
  classical
  let hle := selectedGraph_le T A
  let e : A ≃ D := Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; omega)
  choose a b p hp he using fun K : D ↦ lift_path_subgraph hle (hD.1 K.val K.property)
  let s (i : Fin k) := if hi : i ∈ A then a (e ⟨i,hi⟩) else T.start i
  let t (i : Fin k) := if hi : i ∈ A then b (e ⟨i,hi⟩) else T.finish i
  have hex (i : Fin k) : ∃ q : G.Walk (s i) (t i), q.IsTrail ∧
      (∀ hi : i ∈ A, q.toSubgraph=(e ⟨i,hi⟩).val.map (Hom.ofLE hle)) ∧
      (i ∉ A → q.toSubgraph=(T.walk i).toSubgraph) ∧ (i ∈ A → q.IsPath) := by
    by_cases hi : i ∈ A
    · rw [show s i=a (e ⟨i,hi⟩) by simp [s,hi],show t i=b (e ⟨i,hi⟩) by simp [t,hi]]
      exact ⟨p (e ⟨i,hi⟩),(hp (e ⟨i,hi⟩)).isTrail,fun _ ↦ (he _).symm,
        fun hn ↦ (hn hi).elim,fun _ ↦ hp _⟩
    · rw [show s i=T.start i by simp [s,hi],show t i=T.finish i by simp [t,hi]]
      exact ⟨T.walk i,T.isTrail i,fun hh ↦ (hi hh).elim,fun _ ↦ rfl,fun hh ↦ (hi hh).elim⟩
  choose q hq hqin hqout hqp using hex
  have hdis : Pairwise fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet := by
    intro i j hij
    by_cases hi : i ∈ A
    · rw [hqin i hi,edgeSet_lift]
      by_cases hj : j ∈ A
      · rw [hqin j hj,edgeSet_lift]
        exact hD.2.1 (e ⟨i,hi⟩).property (e ⟨j,hj⟩).property
          (fun h ↦ hij (congrArg Subtype.val (e.injective (Subtype.ext h))))
      · rw [hqout j hj]
        exact (selected_disjoint T A j hj).mono_left (e ⟨i,hi⟩).val.edgeSet_subset
    · rw [hqout i hi]
      by_cases hj : j ∈ A
      · rw [hqin j hj,edgeSet_lift]
        exact ((selected_disjoint T A i hi).mono_left (e ⟨j,hj⟩).val.edgeSet_subset).symm
      · rw [hqout j hj]
        exact T.disjoint hij
  have hcover : ∀ d, d ∈ G.edgeSet ↔ ∃ i, d ∈ (q i).toSubgraph.edgeSet := by
    intro d
    constructor
    · intro hd
      obtain ⟨i,hi⟩ := (T.cover d).mp hd
      by_cases hia : i ∈ A
      · have hdJ : d ∈ (selectedGraph T A).edgeSet := (selected_edge_iff T A d).mpr ⟨i,hia,hi⟩
        rw [←hD.2.2] at hdJ
        obtain ⟨K,hK⟩ := Set.mem_iUnion.mp hdJ
        obtain ⟨hKD,hdK⟩ := Set.mem_iUnion.mp hK
        let j := e.symm ⟨K,hKD⟩
        refine ⟨j.val,?_⟩
        rw [hqin j.val j.property,edgeSet_lift]
        change d ∈ (e (e.symm ⟨K,hKD⟩)).val.edgeSet
        rw [e.apply_symm_apply]
        exact hdK
      · exact ⟨i,by rw [hqout i hia]; exact hi⟩
    · rintro ⟨i,hi⟩
      exact (q i).toSubgraph.edgeSet_subset hi
  let U : TrailFamily G k := ⟨s,t,q,hq,hdis,hcover⟩
  have hdef (i : Fin k) : U.defect i=T.defect i := by
    by_cases hi : i ∈ A
    · rw [(U.defect_eq_zero_iff i).mpr (hqp i hi),(T.defect_eq_zero_iff i).mpr (hpA i hi)]
    · have hpart : (U.walk i).toSubgraph=(T.walk i).toSubgraph := hqout i hi
      have hlen : (U.walk i).length=(T.walk i).length := by
        rw [←trail_edgeSet_ncard _ (U.isTrail i),hpart,trail_edgeSet_ncard _ (T.isTrail i)]
      change (U.walk i).length+1-(U.walk i).toSubgraph.verts.ncard =
        (T.walk i).length+1-(T.walk i).toSubgraph.verts.ncard
      rw [hlen,hpart]
  have hscore : U.score=T.score := by
    have hU := U.sum_defect_add_score
    have hT := T.sum_defect_add_score
    simp_rw [hdef] at hU
    omega
  refine ⟨U,hscore,?_,hqp,?_,?_⟩
  · intro i hi
    exact ⟨by simp [U,s,hi],by simp [U,t,hi],hqout i hi⟩
  · intro i hi
    exact ⟨(e ⟨i,hi⟩).val,(e ⟨i,hi⟩).property,hqin i hi⟩
  · intro K hK
    let i := e.symm ⟨K,hK⟩
    refine ⟨i.val,i.property,?_⟩
    change (q i.val).toSubgraph=K.map (Hom.ofLE hle)
    rw [hqin i.val i.property]
    change (e (e.symm ⟨K,hK⟩)).val.map (Hom.ofLE hle)=_
    rw [e.apply_symm_apply]

/-- A whole outside group may be reoptimized to expose a desired neighbor
of the repeated start. This then triggers the ordinary endpoint slide. -/
lemma repair_with_marked_outside_group (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k) (hi : ¬(T.walk i).IsPath)
    {a x b : V} (hai : T.start i=a) (hbi : T.finish i=b)
    (h : G.Adj a x) (p : G.Walk x b) (ht : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : a ∈ p.support)
    (A : Finset (Fin k)) (hia : i ∉ A) (hav : ∀ j ∈ A, a ∉ (T.walk j).support)
    (D : Finset (selectedGraph T A).Subgraph) (hD : GoodDecomposition (selectedGraph T A) D)
    (hcard : D.card=A.card) {y : V} (P : (selectedGraph T A).Walk x y)
    (hP : P.IsPath) (hnP : ¬P.Nil) (hPD : P.toSubgraph ∈ D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  classical
  obtain ⟨U,hUs,hrest,hpaths,_,hparts⟩ := replace_path_group_tracked T A
    (fun j hj ↦ (T.one_defect_other_paths hs i hi).2 j (fun h ↦ hia (h ▸ hj))) D hD hcard
  obtain ⟨j,hj,hUj⟩ := hparts P.toSubgraph hPD
  have hij : i ≠ j := fun h ↦ hia (h.symm ▸ hj)
  let Q := P.mapLe (selectedGraph_le T A)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T A)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hends : x=U.start j ∨ x=U.finish j := MarkedBudgets.endpoint_of_path_rep Q hQ
    (U.walk j) (U.isTrail j) (hUj.trans hQe.symm)
  have havoid : a ∉ (U.walk j).support := by
    intro ha
    have haQ : a ∈ Q.support := by
      rw [←Walk.mem_verts_toSubgraph,hUj,←hQe,Walk.mem_verts_toSubgraph] at ha
      exact ha
    have haP : a ∈ P.support := by simpa only [Q,Walk.support_mapLe_eq_support] using haQ
    have haJ : a ∈ (selectedGraph T A).support := path_support_subset_graph_support hP hnP a haP
    obtain ⟨z,l,hl,hal⟩ := haJ
    exact hav l hl (Walk.mem_support_of_adj_toSubgraph hal)
  obtain ⟨W,hWs,_,hWj,hWends,hWparts⟩ := orient_endpoint_start U j x hends
  obtain ⟨hUia,hUib,hUi⟩ := hrest i hia
  obtain ⟨hWia,hWib⟩ := hWends i hij
  obtain ⟨Z,_,hZ⟩ := repair_at_outside_start_endpoints W (by omega) i j hij
    (hWia.trans (hUia.trans hai)) hWj (hWib.trans (hUib.trans hbi)) h p ht
    ((hWparts i).trans (hUi.trans he)) hr (by
      intro ha
      apply havoid
      rw [←Walk.mem_verts_toSubgraph,hWparts,Walk.mem_verts_toSubgraph] at ha
      exact ha)
  exact MatchingAppend.path_family_partition Z hZ

/-- At the conjectured budget, a tight connected normal group wholly
avoiding a repeated start cannot contain its exposed first neighbor. -/
lemma tight_outside_group_misses_neighbor {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hi : ¬(T.walk i).IsPath)
    {a x b : Fin n} (hai : T.start i=a) (hbi : T.finish i=b)
    (h : G.Adj a x) (p : G.Walk x b) (ht : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : a ∈ p.support)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
    (hia : i ∉ A) (hav : ∀ j ∈ A, a ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1) :
    x ∉ (selectedGraph T A).support := by
  intro hx
  obtain ⟨D,y,P,hD,hcard,hP,hnP,hPD⟩ := tight_normal_group_marked hsmall hfail T hs i hi A hia hc htight x hx
  exact hfail (repair_with_marked_outside_group T hs i hi hai hbi h p ht he hr A hia hav D hD hcard P hP hnP hPD)

/-- Both neighbors of the root on its chosen cycle are excluded from every
tight connected outside group. Reversing the cycle exposes either edge while
the attached tail stays fixed. -/
lemma rooted_cycle_tight_group_avoids_neighbors {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1)
    {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x) :
    x ∉ (selectedGraph T A).support := by
  have hia : L.index ∉ A := by
    intro hi
    apply hav L.index hi
    exact Eq.mp (congrArg (fun v : Fin n ↦ v ∈ (T.walk L.index).support) L.start_eq)
      (T.walk L.index).start_mem_support
  let h := L.cycle.toSubgraph.adj_sub hx
  obtain ⟨Q,hQ,hQe⟩ := CycleFirstVisits.cycle_edge_first L.cycle L.isCycle h
    (L.cycle.mem_edges_toSubgraph.mp hx)
  let p := Q.append L.tail
  have ht : (Walk.cons h p).IsTrail := by
    change ((Walk.cons h Q).append L.tail).IsTrail
    apply trail_append_of_disjoint hQ.isTrail L.isPath.isTrail
    rw [hQe]
    exact LollipopEar.edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter
  have he : (T.walk L.index).toSubgraph=(Walk.cons h p).toSubgraph := by
    change (T.walk L.index).toSubgraph=((Walk.cons h Q).append L.tail).toSubgraph
    rw [L.subgraph,Walk.toSubgraph_append,Walk.toSubgraph_append,hQe]
  have hr : r ∈ p.support := by
    rw [Walk.mem_support_append_iff]
    exact Or.inl Q.end_mem_support
  exact tight_outside_group_misses_neighbor hsmall hfail T hs L.index L.member_not_path
    L.start_eq L.finish_eq h p ht he hr A hia hav hc htight

lemma outside_group_meeting_cycle_neighbor_expands {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x) (hxA : x ∈ (selectedGraph T A).support) :
    2*A.card ≤ (selectedGraph T A).support.ncard := by
  have hia : L.index ∉ A := by
    intro hi
    apply hav L.index hi
    exact Eq.mp (congrArg (fun v : Fin n ↦ v ∈ (T.walk L.index).support) L.start_eq)
      (T.walk L.index).start_mem_support
  have hb := normal_group_expands hsmall hfail T hs L.index L.member_not_path A hia hc
  have hn : 2*A.card ≠ (selectedGraph T A).support.ncard+1 := by
    intro heq
    exact rooted_cycle_tight_group_avoids_neighbors hsmall hfail T hs r L A hav hc heq hx hxA
  omega

end Erdos583GroupActivationDevelopment
