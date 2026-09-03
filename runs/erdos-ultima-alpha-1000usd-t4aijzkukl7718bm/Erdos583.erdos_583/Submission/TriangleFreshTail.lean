import Submission.LollipopComponentSuppression

/-! A triangular lollipop with an arbitrary fresh tail absorbs a touching path.
The tail is explicitly required to be vertex-disjoint from that other path. -/
namespace Erdos583TriangleFreshTailDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.TriangleAbsorption Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma triangle_fresh_tail_at_last {r v w t a b : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (S : G.Walk r t) (hS : S.IsPath) (hvS : v ∉ S.support) (hwS : w ∉ S.support)
    (A : G.Walk a w) (D : G.Walk w b) (hp : (A.append D).IsPath)
    (hSP : Disjoint S.toSubgraph.verts (A.append D).toSubgraph.verts)
    (hvD : v ∉ D.support)
    (havoid : ∀ e ∈ ({s(r,v),s(v,w),s(r,w)} : Set (Sym2 V)),
      e ∉ (A.append D).toSubgraph.edgeSet) :
    TwoPathCover (G := G) (((A.append D).toSubgraph.edgeSet ∪ {s(r,v),s(v,w),s(r,w)}) ∪ S.toSubgraph.edgeSet) := by
  have hAP (z) (hz : z ∈ A.support) : z ∈ (A.append D).support := (Walk.mem_support_append_iff _ _).mpr (Or.inl hz)
  have hDP (z) (hz : z ∈ D.support) : z ∈ (A.append D).support := (Walk.mem_support_append_iff _ _).mpr (Or.inr hz)
  have hno (z) (hzS : z ∈ S.support) (hzP : z ∈ (A.append D).support) : False :=
    Set.disjoint_left.mp hSP (S.mem_verts_toSubgraph.mpr hzS) ((A.append D).mem_verts_toSubgraph.mpr hzP)
  have hrA : r ∉ A.support := fun hz ↦ hno r S.start_mem_support (hAP r hz)
  have hrD : r ∉ D.support := fun hz ↦ hno r S.start_mem_support (hDP r hz)
  let X := Walk.cons hrw A.reverse
  let Y := Walk.cons hrv (Walk.cons hvw D)
  have hX : X.IsPath := (Walk.cons_isPath_iff hrw A.reverse).mpr
    ⟨hp.of_append_left.reverse,by simpa only [Walk.support_reverse,List.mem_reverse] using hrA⟩
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨hp.of_append_right,hvD⟩,hrv.ne,hrD⟩
  have hcover : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=
      (A.append D).toSubgraph.edgeSet ∪ {s(r,v),s(v,w),s(r,w)} := by
    ext e
    simp only [X,Y,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,Walk.edges_append,
      List.mem_cons,List.mem_reverse,List.mem_append,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hlength : X.length+Y.length=
      ((A.append D).toSubgraph.edgeSet ∪ {s(r,v),s(v,w),s(r,w)}).ncard := by
    rw [triangle_union_ncard hrv hvw hrw _ hp havoid]
    simp only [X,Y,Walk.length_cons,Walk.length_reverse,Walk.length_append]
    omega
  have hdis := disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ hcover hlength
  have hZX : (S.reverse.append X).IsPath := by
    apply path_append_of_support_intersection hS.reverse hX
    intro z hzS hzX
    have hzS' : z ∈ S.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hzS
    simp only [X,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse] at hzX
    exact hzX.elim id (fun hzA ↦ (hno z hzS' (hAP z hzA)).elim)
  have hSY : Disjoint S.toSubgraph.edgeSet Y.toSubgraph.edgeSet := by
    apply edge_disjoint_of_one_common_vertex S Y
    intro z hzS hzY
    simp only [Y,Walk.support_cons,List.mem_cons] at hzY
    rcases hzY with rfl | rfl | hzD
    · rfl
    · exact (hvS hzS).elim
    · exact (hno z hzS (hDP z hzD)).elim
  refine ⟨t,a,r,b,S.reverse.append X,Y,hZX,hY,?_,?_⟩
  · rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup,Walk.toSubgraph_reverse]
    exact disjoint_sup_left.mpr ⟨hSY,hdis⟩
  · rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup,Walk.toSubgraph_reverse,
      Set.union_assoc,hcover,Set.union_comm]

lemma triangle_fresh_tail_absorption {r x y t a b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (S : G.Walk r t) (hS : S.IsPath) (hxS : x ∉ S.support) (hyS : y ∉ S.support)
    (P : G.Walk a b) (hp : P.IsPath)
    (hSP : Disjoint S.toSubgraph.verts P.toSubgraph.verts)
    (hinter : x ∈ P.support ∨ y ∈ P.support)
    (havoid : ∀ e ∈ ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)), e ∉ P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((P.toSubgraph.edgeSet ∪ {s(r,x),s(x,y),s(r,y)}) ∪ S.toSubgraph.edgeSet) := by
  have hhit : ∃ v ∈ P.support, v ∈ ({x,y} : Set V) := by
    rcases hinter with hx|hy
    · exact ⟨x,hx,by simp⟩
    · exact ⟨y,hy,by simp⟩
  obtain ⟨w,hw,A,D,hform,hD⟩ := CycleDefect.last_hit_split P {x,y} hhit
  rw [hform] at hp hSP havoid ⊢
  rcases hw with hw|hw
  · have hw : w=x := hw
    subst w
    have hswap : ({s(r,y),s(y,x),s(r,x)} : Set (Sym2 V))={s(r,x),s(x,y),s(r,y)} := by
      ext e
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := x)]
      tauto
    rw [←hswap] at havoid ⊢
    exact triangle_fresh_tail_at_last hry hxy.symm hrx S hS hyS hxS A D hp hSP
      (fun hy ↦ hxy.ne.symm (hD y hy (by simp))) havoid
  · have hw : w=y := hw
    subst w
    exact triangle_fresh_tail_at_last hrx hxy hry S hS hxS hyS A D hp hSP
      (fun hx ↦ hxy.ne (hD x hx (by simp))) havoid

lemma maximum_triangle_tail_avoider_misses_cycle {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (j : Fin k) (hij : L.index ≠ j)
    (hTail : Disjoint L.tail.toSubgraph.verts (T.walk j).toSubgraph.verts) :
    Disjoint L.cycle.toSubgraph.verts (T.walk j).toSubgraph.verts := by
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hc
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hxS : x ∉ L.tail.support := fun hx ↦ hrx.ne.symm (L.inter x hxC hx)
  have hyS : y ∉ L.tail.support := fun hy ↦ hyr.ne (L.inter y hyC hy)
  have heC : L.cycle.toSubgraph.edgeSet={s(r,x),s(x,y),s(r,y)} := by
    rw [hC]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hd : Disjoint (T.walk L.index).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := T.disjoint hij
  rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hd
  have havoid : ∀ e ∈ ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)), e ∉ (T.walk j).toSubgraph.edgeSet := by
    intro e he hj
    exact Set.disjoint_left.mp (disjoint_sup_left.mp hd).1 (heC.symm ▸ he) hj
  apply Set.disjoint_left.mpr
  intro z hzC hzP
  have hzC' := L.cycle.mem_verts_toSubgraph.mp hzC
  have hzP' := (T.walk j).mem_verts_toSubgraph.mp hzP
  have hrP : r ∉ (T.walk j).support := fun hh ↦ Set.disjoint_left.mp hTail
    L.tail.start_mem_verts_toSubgraph ((T.walk j).mem_verts_toSubgraph.mpr hh)
  have hinter : x ∈ (T.walk j).support ∨ y ∈ (T.walk j).support := by
    simp only [hC,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hzC'
    rcases hzC' with rfl|rfl|rfl|rfl
    · exact (hrP hzP').elim
    · exact Or.inl hzP'
    · exact Or.inr hzP'
    · exact (hrP hzP').elim
  have hh := triangle_fresh_tail_absorption hrx hxy hyr.symm L.tail L.isPath hxS hyS
    (T.walk j) hp hTail hinter havoid
  apply ShortLollipop.maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup,heC]
  have hu : ({s(r,x),s(x,y),s(r,y)} ∪ L.tail.toSubgraph.edgeSet) ∪ (T.walk j).toSubgraph.edgeSet =
      ((T.walk j).toSubgraph.edgeSet ∪ {s(r,x),s(x,y),s(r,y)}) ∪ L.tail.toSubgraph.edgeSet := by ac_rfl
  rw [hu]
  exact hh


lemma maximum_triangle_component_meets_tail {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (A : (normalGraph T L.index).ConnectedComponent) :
    ¬Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support := by
  intro hTail
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  obtain ⟨z,hzL,hzA⟩ := component_meets_removed T hG L.index hn A
  have hzC : z ∈ L.cycle.toSubgraph.verts := by
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.verts_sup] at hzL
    exact hzL.elim id (fun hzT ↦ (Set.disjoint_left.mp hTail hzT hzA).elim)
  obtain ⟨y,j,hj,hzj⟩ := hzA
  have hji := ((mem_componentMembers T L.index j A).mp hj).1
  have hTailP : Disjoint L.tail.toSubgraph.verts (T.walk j).toSubgraph.verts := by
    apply hTail.mono_right
    intro x hx
    rw [selected_support_eq T (componentMembers T L.index A) (fun j _ ↦ hn j)]
    exact ⟨j,hj,(T.walk j).mem_verts_toSubgraph.mp hx⟩
  exact Set.disjoint_left.mp (maximum_triangle_tail_avoider_misses_cycle T hs hm r L hc j hji.symm hTailP)
    hzC ((T.walk j).toSubgraph.edge_vert hzj)


lemma maximum_triangle_component_count {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3) :
    Nat.card (normalGraph T L.index).ConnectedComponent ≤ L.tail.length+1 := by
  have hex (A : (normalGraph T L.index).ConnectedComponent) :
      ∃ x, x ∈ L.tail.toSubgraph.verts ∧ x ∈ (selectedGraph T (componentMembers T L.index A)).support :=
    Set.not_disjoint_iff.mp (maximum_triangle_component_meets_tail T hG hs hm r L hc A)
  choose f hfT hfS using hex
  let g (A : (normalGraph T L.index).ConnectedComponent) : L.tail.toSubgraph.verts := ⟨f A,hfT A⟩
  have hg : Function.Injective g := by
    intro A B he
    by_contra hAB
    have hh : f A=f B := congrArg Subtype.val he
    exact Set.disjoint_left.mp (component_support_disjoint T L.index hAB) (hfS A) (hh.symm ▸ hfS B)
  have hh := Fintype.card_le_of_injective g hg
  simpa only [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,
    InducedBuffer.path_vertex_ncard L.tail L.isPath] using hh

end Erdos583TriangleFreshTailDevelopment
