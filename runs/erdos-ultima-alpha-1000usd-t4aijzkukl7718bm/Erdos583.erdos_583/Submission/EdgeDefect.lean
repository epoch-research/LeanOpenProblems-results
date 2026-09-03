import Submission.Work

/-! A one-edge extension produces at most one rooted incidence defect.
No unrestricted defect normalization theorem is assumed. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.QuotaRooted
namespace Erdos583EdgeDefectDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma decomposition_path_family {V : Type*} {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : GoodDecomposition G D) :
    ∃ T : TrailFamily G D.card, (∀ i, (T.walk i).IsPath) ∧
      ∀ K ∈ D, ∃ i, (T.walk i).toSubgraph=K := by
  classical
  choose a b p hp he using fun K : D ↦ hD.1 K.val K.property
  let e : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (by simp)).symm
  let T : TrailFamily G D.card :=
    { start := a ∘ e, finish := b ∘ e, walk := fun i ↦ p (e i),
      isTrail := fun i ↦ (hp (e i)).isTrail,
      disjoint := by
        intro i j hij
        rw [←he,←he]
        exact hD.2.1 (e i).property (e j).property
          (fun h ↦ hij (e.injective (Subtype.ext h)))
      cover := by
        intro d
        rw [←hD.2.2]
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨K,hK,hd⟩
          refine ⟨e.symm ⟨K,hK⟩,?_⟩
          rw [←he]
          simpa only [e.apply_symm_apply] using hd
        · rintro ⟨i,hi⟩
          exact ⟨(e i).val,(e i).property,by rwa [←he] at hi⟩ }
  refine ⟨T,fun i ↦ hp (e i),?_⟩
  intro K hK
  refine ⟨e.symm ⟨K,hK⟩,?_⟩
  change (p (e (e.symm ⟨K,hK⟩))).toSubgraph=K
  rw [e.apply_symm_apply,←he]

lemma decomposition_odd_endpoint {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : GoodDecomposition G D) (u : V)
    (hu : Odd (Nat.card (G.neighborSet u))) :
    ∃ T : TrailFamily G D.card, (∀ i, (T.walk i).IsPath) ∧
      ∃ i, u=T.start i ∨ u=T.finish i := by
  classical
  obtain ⟨T,hT,hparts⟩ := decomposition_path_family D hD
  have hu' : Odd (G.degree u) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hu
  have hodd := (hD.odd_endpointMultiplicity_iff u).mpr hu'
  have hpos : 0 < (D.filter fun K ↦ (K.neighborSet u).ncard=1).card := hodd.pos
  obtain ⟨K,hK⟩ := Finset.card_pos.mp hpos
  obtain ⟨hKD,hd⟩ := Finset.mem_filter.mp hK
  obtain ⟨i,hi⟩ := hparts K hKD
  have hlocal : Odd ((T.walk i).toSubgraph.neighborSet u).ncard := by rw [hi,hd]; exact odd_one
  exact ⟨T,hT,i,((trail_neighbor_ncard_odd_iff (T.isTrail i) u).mp hlocal).2⟩

/-- Append one genuinely new edge to one endpoint of a path partition.
The indexed cardinality is unchanged and the total incidence defect is at
most one. In the nonpath case the defect is rooted at the new endpoint. -/
lemma append_new_edge {V : Type*} [Fintype V] {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G) (T : TrailFamily H k) (hpath : ∀ i, (T.walk i).IsPath)
    (i : Fin k) {u v : V} (hui : u=T.start i ∨ u=T.finish i)
    (h : G.Adj v u) (hnew : s(v,u) ∉ H.edgeSet)
    (hcover : G.edgeSet=insert s(v,u) H.edgeSet) :
    ∃ U : TrailFamily G k,
      G.edgeSet.ncard+k ≤ U.score+1 ∧
      (¬(∀ l, (U.walk l).IsPath) → HasRoot U v) := by
  classical
  obtain ⟨S,_,_,hSi,_,hparts⟩ := orient_endpoint_start T i u hui
  have hSpath (l : Fin k) : (S.walk l).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (S.isTrail l) (hpath l) (hparts l)
  let p (l : Fin k) := (S.walk l).mapLe hHG
  have hp (l : Fin k) : (p l).IsPath := (hSpath l).mapLe hHG
  have hpe (l : Fin k) : (p l).toSubgraph.edgeSet=(S.walk l).toSubgraph.edgeSet := by
    simp [p,Walk.mapLe]
  have h' : G.Adj v (S.start i) := by rw [hSi]; exact h
  have hne (l : Fin k) : s(v,u) ∉ (p l).toSubgraph.edgeSet := by
    rw [hpe]
    exact fun hh ↦ hnew ((S.walk l).toSubgraph.edgeSet_subset hh)
  let r := Walk.cons h' (p i)
  have hr : r.IsTrail := (hp i).isTrail.cons h' (by
    intro hh
    apply hne i
    rw [←hSi]
    exact (p i).mem_edges_toSubgraph.mpr hh)
  have hre : r.toSubgraph.edgeSet=insert s(v,u) (p i).toSubgraph.edgeSet := by
    simp [r,hSi]
  have hrbound : r.length+1 ≤ r.toSubgraph.verts.ncard+1 := by
    have hh := Set.ncard_le_ncard (show (p i).toSubgraph.verts ⊆ r.toSubgraph.verts by
      simp only [r,Walk.toSubgraph,Subgraph.verts_sup]
      exact Set.subset_union_right)
    rw [(walk_vertex_ncard_eq_iff (p i)).mpr (hp i)] at hh
    simpa only [r,Walk.length_cons] using Nat.add_le_add_right hh 1
  let a (l : Fin k) := if l=i then v else S.start l
  have hex (l : Fin k) : ∃ q : G.Walk (a l) (S.finish l), q.IsTrail ∧
      q.toSubgraph.edgeSet=(if l=i then insert s(v,u) (p l).toSubgraph.edgeSet else (p l).toSubgraph.edgeSet) ∧
      (l=i → q.toSubgraph=r.toSubgraph) ∧
      (l ≠ i → q.IsPath) ∧
      q.length+1 ≤ q.toSubgraph.verts.ncard+(if l=i then 1 else 0) := by
    by_cases hl : l=i
    · subst l
      rw [show a i=v by simp [a]]
      exact ⟨r,hr,by simpa using hre,fun _ ↦ rfl,fun hn ↦ (hn rfl).elim,by simpa using hrbound⟩
    · rw [show a l=S.start l by simp [a,hl]]
      refine ⟨p l,(hp l).isTrail,by simp [hl],fun hh ↦ (hl hh).elim,fun _ ↦ hp l,?_⟩
      rw [(walk_vertex_ncard_eq_iff (p l)).mpr (hp l)]
      simp only [if_neg hl,Nat.add_zero,le_refl]
  choose q hq hqe hqr hqp hqb using hex
  let U : TrailFamily G k :=
    { start := a, finish := S.finish, walk := q, isTrail := hq,
      disjoint := by
        intro l m hlm
        rw [hqe,hqe]
        have hd : Disjoint (p l).toSubgraph.edgeSet (p m).toSubgraph.edgeSet := by
          rw [hpe,hpe]; exact S.disjoint hlm
        by_cases hl : l=i
        · subst l
          simp only [if_neg hlm.symm]
          exact Set.disjoint_insert_left.mpr ⟨hne m,hd⟩
        · by_cases hm : m=i
          · subst m
            simp only [if_neg hl]
            exact Set.disjoint_insert_right.mpr ⟨hne l,hd⟩
          · simpa only [if_neg hl,if_neg hm] using hd
      cover := by
        intro d
        rw [hcover,Set.mem_insert_iff]
        constructor
        · rintro (rfl|hd)
          · refine ⟨i,?_⟩
            rw [hqe]; simp
          · obtain ⟨l,hl⟩ := (S.cover d).mp hd
            refine ⟨l,?_⟩
            rw [hqe,←hpe] at *
            split_ifs
            · exact Set.mem_insert_of_mem _ hl
            · exact hl
        · rintro ⟨l,hl⟩
          rw [hqe] at hl
          split_ifs at hl with hh
          · rcases hl with he|he
            · exact Or.inl he
            · exact Or.inr ((S.cover d).mpr ⟨l,by rwa [hpe] at he⟩)
          · exact Or.inr ((S.cover d).mpr ⟨l,by rwa [hpe] at hl⟩) }
  refine ⟨U,?_,?_⟩
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦ hqb l)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hh
    have hlen : ∑ l, (q l).length=G.edgeSet.ncard := U.sum_length
    have hscore : ∑ l, (q l).toSubgraph.verts.ncard=U.score := rfl
    simpa only [hlen,hscore,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh
  · intro hn
    have hri : ¬r.IsPath := by
      intro hP
      apply hn
      intro l
      by_cases hl : l=i
      · subst l
        exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (hq i) hP (hqr i rfl)
      · exact hqp l hl
    have hv : v ∈ (p i).support := by
      by_contra hh
      exact hri ((Walk.cons_isPath_iff h' (p i)).mpr ⟨hp i,hh⟩)
    exact hasRoot_of_rep U i (by simp [U,a]) rfl h' (p i) (hqr i rfl) hr hv

lemma even_degree_delete_edge_odd {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u))) :
    Odd (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet u)) := by
  classical
  let H := G.deleteEdges {s(v,u)}
  have hN : G.neighborSet u=insert v (H.neighborSet u) := by
    ext w
    by_cases hw : w=v
    · subst w
      simp [h.symm]
    · simp [H,mem_neighborSet,hw,deleteEdges_adj,h.ne.symm]
  have hv : v ∉ H.neighborSet u := by simp [H,mem_neighborSet,Sym2.eq_swap]
  have hc := Set.ncard_insert_of_notMem hv
  rw [←hN] at hc
  have hd : Nat.card (G.neighborSet u)=Nat.card (H.neighborSet u)+1 := by
    simpa only [Nat.card_coe_set_eq] using hc
  exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp (by rwa [←hd]))

/-- If deleting an edge at an even-degree vertex already has a bounded path
partition, any failure of that bound after restoration has a globally maximal
family with exactly one rooted defect. This does not assert that the deletion
hypothesis is available for every graph. -/
lemma one_defect_of_even_edge_deletion {V : Type*} [Fintype V]
    {G : SimpleGraph V} {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (k : ℕ) (D : Finset (G.deleteEdges {s(v,u)}).Subgraph)
    (hD : GoodDecomposition (G.deleteEdges {s(v,u)}) D) (hcard : D.card ≤ k)
    (hfail : ¬∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k) :
    ∃ U : TrailFamily G k, U.score+1=G.edgeSet.ncard+k ∧ HasRoot U v ∧
      ∀ S : TrailFamily G k, S.score ≤ U.score := by
  classical
  have hcardeq : D.card=k := by
    by_contra hn
    have hpK : IsPathSubgraph (G.subgraphOfAdj h) :=
      ⟨v,u,Walk.cons h Walk.nil,by simp [h.ne],by simp⟩
    have hrestore := @restore_path_subgraph V G (G.subgraphOfAdj h) hpK
    rw [G.edgeSet_subgraphOfAdj h] at hrestore
    obtain ⟨E,hE,hEc⟩ := hrestore hD
    exact hfail ⟨E,hE,by omega⟩
  have hodd : Odd (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet u)) :=
    even_degree_delete_edge_odd (G := G) (u := u) (v := v) h hu
  obtain ⟨T,hT,i,hi⟩ := decomposition_odd_endpoint (G := G.deleteEdges {s(v,u)}) D hD u hodd
  have hnew : s(v,u) ∉ (G.deleteEdges {s(v,u)}).edgeSet := by simp
  have hcover : G.edgeSet=insert s(v,u) (G.deleteEdges {s(v,u)}).edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from h)).symm
  obtain ⟨U,hU,hroot⟩ := append_new_edge (G.deleteEdges_le _) T hT i hi h hnew hcover
  have hnp (W : TrailFamily G D.card) : ¬∀ l, (W.walk l).IsPath := by
    intro hp
    obtain ⟨E,hE,hEc⟩ := MatchingAppend.path_family_partition W hp
    exact hfail ⟨E,hE,hEc.trans hcard⟩
  have hs : U.score+1=G.edgeSet.ncard+D.card := by
    have hb := U.score_le_edges_add
    have hn := (U.score_eq_edges_add_iff).not.mpr (hnp U)
    omega
  have hm (W : TrailFamily G D.card) : W.score ≤ U.score := by
    have hb := W.score_le_edges_add
    have hn := (W.score_eq_edges_add_iff).not.mpr (hnp W)
    omega
  have hh : ∃ U : TrailFamily G D.card, U.score+1=G.edgeSet.ncard+D.card ∧ HasRoot U v ∧
      ∀ W : TrailFamily G D.card, W.score ≤ U.score := ⟨U,hs,hroot (hnp U),hm⟩
  rwa [hcardeq] at hh

lemma closed_trail_has_nonbridge_at_root {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsTrail) (hn : ¬c.Nil) :
    ∃ w, G.Adj v w ∧ ¬G.IsBridge s(v,w) := by
  cases c with
  | nil => exact (hn Walk.Nil.nil).elim
  | @cons v w v h p =>
    refine ⟨w,h,?_⟩
    intro hb
    have he := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hb).2 p.reverse
    exact (Walk.isTrail_cons h p).mp hc |>.2 (by simpa using he)

lemma intersecting_trails_have_nonbridge_at_root {V : Type*} {G : SimpleGraph V}
    {v a b x : V} (p : G.Walk v a) (q : G.Walk v b)
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hd : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hx : x ≠ v) (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    ∃ w, G.Adj v w ∧ ¬G.IsBridge s(v,w) := by
  classical
  let P := p.takeUntil x hxp
  let Q := q.takeUntil x hxq
  have hP : P.IsTrail := hp.takeUntil hxp
  have hQ : Q.IsTrail := hq.takeUntil hxq
  have hd' : Disjoint P.toSubgraph.edgeSet Q.reverse.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_reverse]
    apply Set.disjoint_left.mpr
    intro e heP heQ
    exact Set.disjoint_left.mp hd
      (p.mem_edges_toSubgraph.mpr (p.edges_takeUntil_subset hxp (P.mem_edges_toSubgraph.mp heP)))
      (q.mem_edges_toSubgraph.mpr (q.edges_takeUntil_subset hxq (Q.mem_edges_toSubgraph.mp heQ)))
  have hc := trail_append_of_disjoint hP hQ.reverse hd'
  have hn : ¬(P.append Q.reverse).Nil := by
    intro hh
    have hl := Walk.nil_iff_length_eq.mp hh
    rw [Walk.length_append] at hl
    have hP0 : P.Nil := Walk.nil_iff_length_eq.mpr (by omega)
    exact Walk.not_nil_of_ne hx.symm hP0
  exact closed_trail_has_nonbridge_at_root _ hc hn

/-- Any graph failing the conjectured count has a nonbridge incident to an
 even-degree vertex. This uses a maximum-inactive normal path partition, not
 an unproved reduction to bridgeless graphs. -/
lemma failure_has_even_nonbridge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ u v, G.Adj v u ∧ Even (Nat.card (G.neighborSet u)) ∧ ¬G.IsBridge s(v,u) := by
  classical
  obtain ⟨D,hD,hne,hb,hmax⟩ := PendantCompletion.exists_max_inactive G
  have htwo : ∃ v, endpointMultiplicity D v=2 := by
    by_contra! hn
    have hsum : ∑ v, endpointMultiplicity D v ≤ Fintype.card V := by
      calc
        _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum (fun v _ ↦ by have := hb v; have := hn v; omega)
        _ = _ := by simp
    rw [hD.sum_endpointMultiplicity hne] at hsum
    have hceil := Nat.le_ceil ((Fintype.card V : ℚ)/2)
    apply hfail
    refine ⟨D,hD,?_⟩
    exact_mod_cast (show (D.card : ℚ) ≤ (⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) by
      have hh : 2*(D.card : ℚ) ≤ Fintype.card V := by exact_mod_cast hsum
      linarith)
  obtain ⟨v,hv⟩ := htwo
  have htwo' : 1 < (D.filter fun K ↦ (K.neighborSet v).ncard=1).card := by
    change 1 < endpointMultiplicity D v
    rw [hv]; decide
  obtain ⟨K,hK,L,hL,hKL⟩ := Finset.one_lt_card.mp htwo'
  obtain ⟨hKD,hKv⟩ := Finset.mem_filter.mp hK
  obtain ⟨hLD,hLv⟩ := Finset.mem_filter.mp hL
  obtain ⟨a,p,hp,hKe⟩ := path_endpoint_of_neighbor_ncard_one (hD.1 K hKD) hKv
  obtain ⟨b,q,hq,hLe⟩ := path_endpoint_of_neighbor_ncard_one (hD.1 L hLD) hLv
  have hP : p.reverse.toSubgraph ∈ D := by simpa only [Walk.toSubgraph_reverse,←hKe] using hKD
  have hQ : q.toSubgraph ∈ D := hLe ▸ hLD
  obtain ⟨x,hx,hxp,hxq⟩ := EndpointSelection.max_inactive_pair_intersects hD hne hb hmax
    p.reverse q hp.reverse hq hP hQ hv
  have hd : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    rw [←hKe,←hLe]
    exact hD.2.1 hKD hLD hKL
  obtain ⟨w,hw,hwb⟩ := intersecting_trails_have_nonbridge_at_root p q hp.isTrail hq.isTrail hd hx
    (by simpa using hxp) hxq
  have heven : Even (G.degree v) := by
    apply Nat.not_odd_iff_even.mp
    rw [←hD.odd_endpointMultiplicity_iff,hv]
    decide
  refine ⟨v,w,hw.symm,?_,?_⟩
  · simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using heven
  · simpa only [Sym2.eq_swap] using hwb

/-- Every connected failure contains, on the same vertex type, a connected
failure whose exact-budget maximum has precisely one rooted defect. The
minimality is over spanning subgraphs with fewer edges; deletion preserves
connectivity because the chosen even-incident edge is not a bridge. -/
lemma failure_has_rooted_one_defect {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) ∧
      ∃ r : V, ∃ T : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊,
        T.score+1=H.edgeSet.ncard+⌈(Fintype.card V : ℚ)/2⌉₊ ∧ HasRoot T r ∧
        ∀ U : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊, U.score ≤ T.score := by
  classical
  let P (n : ℕ) := ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
    (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) ∧
    H.edgeSet.ncard=n
  have hex : ∃ n, P n := ⟨G.edgeSet.ncard,G,le_rfl,hG,hfail,rfl⟩
  obtain ⟨H,hHG,hH,hfailH,hmin⟩ := Nat.find_spec hex
  obtain ⟨u,v,h,hu,hnb⟩ := failure_has_even_nonbridge H hfailH
  have hcon : (H.deleteEdges {s(v,u)}).Connected := hH.connected_delete_edge_of_not_isBridge hnb
  have hDexists : ∃ D : Finset (H.deleteEdges {s(v,u)}).Subgraph,
      GoodDecomposition (H.deleteEdges {s(v,u)}) D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
    by_contra hno
    have hh : P (H.deleteEdges {s(v,u)}).edgeSet.ncard :=
      ⟨H.deleteEdges {s(v,u)},(H.deleteEdges_le _).trans hHG,hcon,hno,rfl⟩
    have hbound := Nat.find_min' hex hh
    have hlt : (H.deleteEdges {s(v,u)}).edgeSet.ncard < H.edgeSet.ncard := by
      rw [edgeSet_deleteEdges]
      exact Set.ncard_diff_singleton_lt_of_mem (show s(v,u) ∈ H.edgeSet from h)
    omega
  obtain ⟨D,hD,hcard⟩ := hDexists
  obtain ⟨T,hs,hr,hm⟩ := one_defect_of_even_edge_deletion h hu _ D hD hcard hfailH
  exact ⟨H,hHG,hH,hfailH,v,T,hs,hr,hm⟩

/-- A precise remaining sufficient statement: rooted single defects at the
exact budget must be repairable. The repair hypothesis is not proved here. -/
lemma gallai_of_rooted_one_defect_repair {V : Type*} [Fintype V]
    (hrepair : ∀ (G : SimpleGraph V), G.Connected → ∀ (r : V)
      (T : TrailFamily G ⌈(Fintype.card V : ℚ)/2⌉₊),
      T.score+1=G.edgeSet.ncard+⌈(Fintype.card V : ℚ)/2⌉₊ → HasRoot T r →
      (∀ U : TrailFamily G ⌈(Fintype.card V : ℚ)/2⌉₊, U.score ≤ T.score) →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  by_contra hn
  obtain ⟨H,_,hH,hfail,r,T,hs,hr,hm⟩ := failure_has_rooted_one_defect G hG hn
  exact hfail (hrepair H hH r T hs hr hm)

end Erdos583EdgeDefectDevelopment
