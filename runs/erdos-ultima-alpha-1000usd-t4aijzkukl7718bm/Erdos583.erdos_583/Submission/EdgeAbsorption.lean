import Submission.Work

/-! Small support partitions after attaching an edge, and tracked path remainders. -/
namespace Erdos583EdgeAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion
open Erdos583Work.MemberNormalExpansion Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 2000000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma attach_edge_support (H : SimpleGraph V) {w x : V} (hw : w ∈ H.support) :
    (H ⊔ edge w x).support ⊆ insert x H.support := by
  rintro z ⟨y,hy⟩
  rcases hy with hy|hy
  · exact Set.mem_insert_of_mem _ ⟨y,hy⟩
  · rcases (edge_adj w x z y).mp hy with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩
    · exact Set.mem_insert_of_mem _ hw
    · exact Set.mem_insert _ _

lemma attach_edge_connected (H : SimpleGraph V) (hc : SupportConnected H)
    {w x : V} (hw : w ∈ H.support) : SupportConnected (H ⊔ edge w x) := by
  have hreach (z : V) (hz : z ∈ (H ⊔ edge w x).support) :
      (H ⊔ edge w x).Reachable z w := by
    rcases attach_edge_support H hw hz with hz|hz
    · subst z
      by_cases h : x=w
      · exact h ▸ Reachable.rfl
      · exact Adj.reachable (Or.inr ((edge_adj w x x w).mpr ⟨Or.inr ⟨rfl,rfl⟩,h⟩))
    · exact (hc z hz w hw).mono le_sup_left
  intro u hu v hv
  exact (hreach u hu).trans (hreach v hv).symm

lemma attach_edge_partition {n t : ℕ} (hsmall : SmallerOrders n)
    [Fintype V] (H : SimpleGraph V) (hc : SupportConnected H)
    {w x : V} (hw : w ∈ H.support)
    (horder : H.support.ncard+1 < n) (hsize : H.support.ncard+1 ≤ 2*t) :
    ∃ D : Finset (H ⊔ edge w x).Subgraph,
      GoodDecomposition (H ⊔ edge w x) D ∧ D.card ≤ t := by
  have hb : (H ⊔ edge w x).support.ncard ≤ H.support.ncard+1 := by
    calc
      _ ≤ (insert x H.support).ncard := Set.ncard_le_ncard (attach_edge_support H hw)
      _ ≤ H.support.ncard+1 := Set.ncard_insert_le _ _
  obtain ⟨D,hD,hcard⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall
    (H ⊔ edge w x) (attach_edge_connected H hc hw) (by omega)
  refine ⟨D,hD,?_⟩
  rw [ceil_half] at hcard
  omega

lemma partition_with_remainder (J : SimpleGraph V) (hJR : J ≤ G)
    (D : Finset J.Subgraph) (hD : GoodDecomposition J D)
    {a b : V} (P : G.Walk a b) (hP : P.IsPath)
    (hd : Disjoint J.edgeSet P.toSubgraph.edgeSet)
    (hcover : J.edgeSet ∪ P.toSubgraph.edgeSet=G.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 ∧
      P.toSubgraph ∈ E ∧
      (∀ K ∈ D, K.map (Hom.ofLE hJR) ∈ E) ∧
      ∀ L ∈ E, L=P.toSubgraph ∨ ∃ K ∈ D, L=K.map (Hom.ofLE hJR) := by
  classical
  let F := D.image (Subgraph.map (Hom.ofLE hJR))
  have hpF : ∀ H ∈ F, IsPathSubgraph H := by
    intro H hH
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨u,v,p,hp,he⟩ := lift_path_subgraph hJR (hD.1 K hK)
    exact ⟨u,v,p,hp,he⟩
  have hpP : ∀ H ∈ ({P.toSubgraph} : Finset G.Subgraph), IsPathSubgraph H := by
    intro H hH
    rw [Finset.mem_singleton.mp hH]
    exact ⟨a,b,P,hP,rfl⟩
  have hE : GoodDecomposition G (F ∪ {P.toSubgraph}) := by
    apply DoubleEndpointGlue.union_partitions_tracked F {P.toSubgraph} hpF hpP
      (hD.2.lift_pairwise hJR)
    · intro H hH K hK hHK
      exact (hHK ((Finset.mem_singleton.mp hH).trans (Finset.mem_singleton.mp hK).symm)).elim
    · intro H hH K hK
      obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hH
      rw [Finset.mem_singleton.mp hK,edgeSet_lift]
      exact hd.mono_left L.edgeSet_subset
    · simpa only [Finset.mem_singleton,Set.iUnion_iUnion_eq_left] using
        (show (⋃ H ∈ F, H.edgeSet) ∪ P.toSubgraph.edgeSet=G.edgeSet by
          rw [hD.2.lift_union hJR,hcover])
  refine ⟨F ∪ {P.toSubgraph},hE,?_,by simp,?_,?_⟩
  · calc
      _ ≤ F.card+({P.toSubgraph} : Finset G.Subgraph).card := Finset.card_union_le _ _
      _ ≤ D.card+1 := by have hh : F.card ≤ D.card := Finset.card_image_le; simp only [Finset.card_singleton]; omega
  · intro K hK
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨K,hK,rfl⟩)
  · intro L hL
    rcases Finset.mem_union.mp hL with hL|hL
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hL
      exact Or.inr ⟨K,hK,rfl⟩
    · exact Or.inl (Finset.mem_singleton.mp hL)

lemma transfer_lift_subgraph {H : SimpleGraph V} (hHG : H ≤ G)
    {a b : V} (P : G.Walk a b) (he : ∀ e ∈ P.edges, e ∈ H.edgeSet) :
    (P.transfer H he).toSubgraph.map (Hom.ofLE hHG)=P.toSubgraph := by
  ext x y
  · simp only [Subgraph.map_verts,Hom.coe_ofLE,Set.image_id,Walk.mem_verts_toSubgraph,
      Walk.support_transfer]
  · change s(x,y) ∈ ((P.transfer H he).toSubgraph.map (Hom.ofLE hHG)).edgeSet ↔
      s(x,y) ∈ P.toSubgraph.edgeSet
    rw [edgeSet_lift]
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_transfer]

noncomputable def reindex (T : TrailFamily G k) (e : Fin k ≃ Fin k) : TrailFamily G k where
  start j := T.start (e j)
  finish j := T.finish (e j)
  walk j := T.walk (e j)
  isTrail j := T.isTrail (e j)
  disjoint _ _ h := T.disjoint (fun hh ↦ h (e.injective hh))
  cover d := by
    rw [T.cover d]
    constructor
    · rintro ⟨j,hj⟩
      refine ⟨e.symm j,?_⟩
      rw [e.apply_symm_apply]
      exact hj
    · rintro ⟨j,hj⟩
      exact ⟨e j,hj⟩

lemma reindex_score (T : TrailFamily G k) (e : Fin k ≃ Fin k) :
    (reindex T e).score=T.score := by
  exact Equiv.sum_comp e (fun j ↦ (T.walk j).toSubgraph.verts.ncard)

lemma same_nonempty_member_unique (T : TrailFamily G k) (j m : Fin k)
    (he : (T.walk j).toSubgraph=(T.walk m).toSubgraph)
    (hn : (T.walk m).toSubgraph.edgeSet.Nonempty) : j=m := by
  by_contra h
  obtain ⟨d,hd⟩ := hn
  exact Set.disjoint_left.mp (T.disjoint h) (he.symm ▸ hd) hd

lemma replace_group_with_distinguished [Fintype V] (T : TrailFamily G k)
    (A : Finset (Fin k)) (hpA : ∀ l ∈ A, (T.walk l).IsPath)
    (D : Finset (selectedGraph T A).Subgraph)
    (hD : GoodDecomposition (selectedGraph T A) D) (hcard : D.card=A.card)
    (j : Fin k) (hjA : j ∈ A) (Q : (selectedGraph T A).Subgraph) (hQ : Q ∈ D)
    (hnQ : Q.edgeSet.Nonempty) :
    ∃ U : TrailFamily G k, U.score=T.score ∧
      (∀ l, l ∉ A → (U.walk l).toSubgraph=(T.walk l).toSubgraph) ∧
      (U.walk j).toSubgraph=Q.map (Hom.ofLE (selectedGraph_le T A)) ∧
      (∀ l ∈ A, l ≠ j → ∃ K ∈ D, K ≠ Q ∧
        (U.walk l).toSubgraph=K.map (Hom.ofLE (selectedGraph_le T A))) ∧
      ∀ K ∈ D, ∃ l ∈ A, (U.walk l).toSubgraph=K.map (Hom.ofLE (selectedGraph_le T A)) := by
  classical
  obtain ⟨Z,hZs,hrest,_,hZin,hparts⟩ := GroupActivation.replace_path_group_tracked T A hpA D hD hcard
  obtain ⟨m,hmA,hm⟩ := hparts Q hQ
  let e := Equiv.swap j m
  let U := reindex Z e
  have heA (l : Fin k) (hl : l ∈ A) : e l ∈ A := by
    by_cases hlj : l=j
    · subst l; simpa only [e,Equiv.swap_apply_left] using hmA
    by_cases hlm : l=m
    · subst l; simpa only [e,Equiv.swap_apply_right] using hjA
    simpa only [e,Equiv.swap_apply_of_ne_of_ne hlj hlm] using hl
  have hUj : (U.walk j).toSubgraph=Q.map (Hom.ofLE (selectedGraph_le T A)) := by
    change (Z.walk (e j)).toSubgraph=_
    rw [show e j=m from Equiv.swap_apply_left j m]
    exact hm
  have hnUj : (U.walk j).toSubgraph.edgeSet.Nonempty := by
    rw [hUj,edgeSet_lift]
    exact hnQ
  refine ⟨U,(reindex_score Z e).trans hZs,?_,hUj,?_,?_⟩
  · intro l hl
    change (Z.walk (e l)).toSubgraph=_
    rw [show e l=l from Equiv.swap_apply_of_ne_of_ne (fun hh ↦ hl (hh ▸ hjA))
      (fun hh ↦ hl (hh ▸ hmA))]
    exact (hrest l hl).2.2
  · intro l hl hlj
    obtain ⟨K,hK,hKe⟩ := hZin (e l) (heA l hl)
    refine ⟨K,hK,?_,hKe⟩
    intro hKQ
    have hlj' : (U.walk l).toSubgraph=(U.walk j).toSubgraph := hKe.trans (hKQ ▸ hUj.symm)
    exact hlj (same_nonempty_member_unique U l j hlj' hnUj)
  · intro K hK
    obtain ⟨l,hl,hKl⟩ := hparts K hK
    refine ⟨e l,heA l hl,?_⟩
    change (Z.walk (e (e l))).toSubgraph=_
    rw [show e (e l)=l from Equiv.swap_apply_self j m l]
    exact hKl

/-- Move the first edge of a normal member into a selected group, keeping its
remaining suffix in the original slot. The new group covers exactly the enlarged
edge union, while every index outside the group and suffix is unchanged. -/
lemma absorb_first_edge [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (hi : ¬(T.walk i).IsPath)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    {w x b : V} (h : G.Adj w x) (q : G.Walk x b)
    (hp : (Walk.cons h q).IsPath) (hqn : ¬q.Nil)
    (hj : (T.walk j).toSubgraph=(Walk.cons h q).toSubgraph)
    (D : Finset (selectedGraph T F ⊔ edge w x).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge w x) D) (hDc : D.card ≤ F.card) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk j).toSubgraph=q.toSubgraph ∧
      (∀ l, l ∉ F → l ≠ j → (U.walk l).toSubgraph=(T.walk l).toSubgraph) ∧
      (∀ l ∈ F, (U.walk l).toSubgraph.edgeSet ⊆ (selectedGraph T F ⊔ edge w x).edgeSet) ∧
      ∀ d ∈ (selectedGraph T F ⊔ edge w x).edgeSet,
        ∃ l ∈ F, d ∈ (U.walk l).toSubgraph.edgeSet := by
  classical
  let A := insert j F
  let R := selectedGraph T A
  let J := selectedGraph T F ⊔ edge w x
  have hia : i ∉ A := by simp [A,hiF,hij]
  have hFle : selectedGraph T F ≤ R := CycleGroupDisjoint.selectedGraph_mono T (Finset.subset_insert _ _)
  have hcons : (Walk.cons h q).toSubgraph.edgeSet ⊆ R.edgeSet := by
    intro d hd
    exact (selected_edge_iff T A d).mpr ⟨j,by simp [A],hj.symm ▸ hd⟩
  have hJR : J ≤ R := by
    apply sup_le hFle
    have hwxR : s(w,x) ∈ R.edgeSet := hcons
      ((Walk.cons h q).mem_edges_toSubgraph.mpr (by simp))
    exact (edge_le_iff R).mpr (Or.inr hwxR)
  have hqle : q.toSubgraph.edgeSet ⊆ R.edgeSet := by
    intro d hd
    apply hcons
    simpa only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] using
      (Or.inr (q.mem_edges_toSubgraph.mp hd) : d=s(w,x) ∨ d ∈ q.edges)
  have hqe : ∀ d ∈ q.edges, d ∈ R.edgeSet := fun d hd ↦ hqle (q.mem_edges_toSubgraph.mpr hd)
  let Q := q.transfer R hqe
  have hQp : Q.IsPath := hp.of_cons.transfer hqe
  have hQe : Q.toSubgraph.edgeSet=q.toSubgraph.edgeSet := by
    ext d
    simp only [Q,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  have hQlift : Q.toSubgraph.map (Hom.ofLE (selectedGraph_le T A))=q.toSubgraph :=
    transfer_lift_subgraph (selectedGraph_le T A) q hqe
  have hdq : Disjoint J.edgeSet q.toSubgraph.edgeSet := by
    rw [show J.edgeSet=(selectedGraph T F).edgeSet ∪ {s(w,x)} from by
      change (selectedGraph T F ⊔ edge w x).edgeSet=_
      rw [edgeSet_sup,edge_edgeSet_of_ne h.ne]]
    apply Set.disjoint_union_left.mpr
    constructor
    · apply (selected_disjoint T F j hjF).mono_right
      rw [hj]
      intro d hd
      simpa only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] using
        (Or.inr (q.mem_edges_toSubgraph.mp hd) : d=s(w,x) ∨ d ∈ q.edges)
    · apply Set.disjoint_singleton_left.mpr
      intro hd
      exact (Walk.isTrail_cons h q).mp hp.isTrail |>.2 (q.mem_edges_toSubgraph.mp hd)
  have hcover : J.edgeSet ∪ Q.toSubgraph.edgeSet=R.edgeSet := by
    rw [hQe,show J.edgeSet=(selectedGraph T F).edgeSet ∪ {s(w,x)} from by
      change (selectedGraph T F ⊔ edge w x).edgeSet=_
      rw [edgeSet_sup,edge_edgeSet_of_ne h.ne]]
    ext d
    simp only [Set.mem_union,Set.mem_singleton_iff,R,selected_edge_iff]
    constructor
    · rintro ((⟨l,hl,hd⟩|hd)|hd)
      · exact ⟨l,Finset.mem_insert_of_mem hl,hd⟩
      · refine ⟨j,by simp [A],?_⟩
        rw [hj,Walk.mem_edges_toSubgraph,Walk.edges_cons]
        exact List.mem_cons.mpr (Or.inl hd)
      · refine ⟨j,by simp [A],?_⟩
        rw [hj,Walk.mem_edges_toSubgraph,Walk.edges_cons]
        exact List.mem_cons.mpr (Or.inr (q.mem_edges_toSubgraph.mp hd))
    · rintro ⟨l,hl,hd⟩
      rcases Finset.mem_insert.mp hl with rfl|hl
      · rw [hj,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] at hd
        rcases hd with hd|hd
        · exact Or.inl (Or.inr hd)
        · exact Or.inr (q.mem_edges_toSubgraph.mpr hd)
      · exact Or.inl (Or.inl ⟨l,hl,hd⟩)
  obtain ⟨E,hE,hEc,hQE,hDE,hEin⟩ := partition_with_remainder J hJR D hD Q hQp
    (by rw [hQe]; exact hdq) hcover
  have hcount : E.card=A.card := by
    have hlo := normal_group_cannot_save hfail T hs i hi A hia E hE
    have hA : A.card=F.card+1 := Finset.card_insert_of_notMem hjF
    omega
  have hnQ : Q.toSubgraph.edgeSet.Nonempty := by
    rw [hQe]
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor q hqn q.start_mem_verts_toSubgraph
    exact ⟨s(x,y),hy⟩
  obtain ⟨U,hUs,hrest,hUj,hUin,hparts⟩ := replace_group_with_distinguished T A
    (fun l hl ↦ (T.one_defect_other_paths hs i hi).2 l (fun hh ↦ hia (hh ▸ hl)))
    E hE hcount j (by simp [A]) Q.toSubgraph hQE hnQ
  have hUjq : (U.walk j).toSubgraph=q.toSubgraph := hUj.trans hQlift
  have hsubset (l : Fin k) (hl : l ∈ F) : (U.walk l).toSubgraph.edgeSet ⊆ J.edgeSet := by
    obtain ⟨K,hK,hnK,hKe⟩ := hUin l (Finset.mem_insert_of_mem hl) (fun hh ↦ hjF (hh ▸ hl))
    rcases hEin K hK with hKQ|⟨L,hL,hLK⟩
    · exact (hnK hKQ).elim
    · rw [hKe,edgeSet_lift,hLK,edgeSet_lift]
      exact L.edgeSet_subset
  refine ⟨U,hUs,hUjq,?_,hsubset,?_⟩
  · intro l hl hlj
    exact hrest l (by simp [A,hl,hlj])
  · intro d hd
    have hdc : d ∈ (⋃ K ∈ D, K.edgeSet) := hD.2.2.symm ▸ hd
    obtain ⟨K,hK⟩ := Set.mem_iUnion.mp hdc
    obtain ⟨hKD,hdK⟩ := Set.mem_iUnion.mp hK
    obtain ⟨l,hl,hKl⟩ := hparts (K.map (Hom.ofLE hJR)) (hDE K hKD)
    have hdl : d ∈ (U.walk l).toSubgraph.edgeSet := by
      rw [hKl,edgeSet_lift,edgeSet_lift]
      exact hdK
    have hlj : l ≠ j := by
      intro hh
      subst l
      rw [hUjq] at hdl
      exact Set.disjoint_left.mp hdq hd hdl
    exact ⟨l,(Finset.mem_insert.mp hl).resolve_left hlj,hdl⟩

end Erdos583EdgeAbsorptionDevelopment
