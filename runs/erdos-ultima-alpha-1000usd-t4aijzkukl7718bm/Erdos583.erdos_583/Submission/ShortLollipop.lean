import Submission.Work

/-! A triangle with a single tail edge can be repaired against any path
avoiding the repeated root and meeting the triangle. Longer attached tails
are not covered by this exchange. -/
namespace Erdos583ShortLollipopDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.TriangleAbsorption
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
/-- Adding a fresh edge at the common start of two paths is harmless when
its other endpoint is absent from at least one of the paths. -/
lemma attach_common_start_edge {r t a b : V} (h : G.Adj r t)
    (P : G.Walk r a) (Q : G.Walk r b) (hp : P.IsPath) (hq : Q.IsPath)
    (hd : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet)
    (hne : s(r,t) ∉ P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet)
    (hav : t ∉ P.support ∨ t ∉ Q.support) :
    TwoPathCover (G := G) (insert s(r,t) (P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet)) := by
  have hnewP : s(r,t) ∉ P.toSubgraph.edgeSet := fun he ↦ hne (Or.inl he)
  have hnewQ : s(r,t) ∉ Q.toSubgraph.edgeSet := fun he ↦ hne (Or.inr he)
  rcases hav with htP|htQ
  · let R := Walk.cons h.symm P
    have hR : R.IsPath := (Walk.cons_isPath_iff h.symm P).mpr ⟨hp,htP⟩
    have hRe : R.toSubgraph.edgeSet=insert s(r,t) P.toSubgraph.edgeSet := by
      ext e
      simp only [R,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,
        Set.mem_insert_iff,Sym2.eq_swap (a := t) (b := r)]
    refine ⟨t,a,r,b,R,Q,hR,hq,?_,?_⟩
    · rw [hRe]
      exact Set.disjoint_insert_left.mpr ⟨hnewQ,hd⟩
    · rw [hRe,Set.insert_union]
  · let R := Walk.cons h.symm Q
    have hR : R.IsPath := (Walk.cons_isPath_iff h.symm Q).mpr ⟨hq,htQ⟩
    have hRe : R.toSubgraph.edgeSet=insert s(r,t) Q.toSubgraph.edgeSet := by
      ext e
      simp only [R,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,
        Set.mem_insert_iff,Sym2.eq_swap (a := t) (b := r)]
    refine ⟨r,a,t,b,P,R,hp,hR,?_,?_⟩
    · rw [hRe]
      exact Set.disjoint_insert_right.mpr ⟨hnewP,hd⟩
    · rw [hRe,Set.union_insert]

lemma triangle_tail_edge_at_last {r v w t a b : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w) (hrt : G.Adj r t)
    (htv : t ≠ v) (htw : t ≠ w)
    (A : G.Walk a w) (D : G.Walk w b) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (hvD : v ∉ D.support)
    (havoid : ∀ e ∈ ({s(r,v),s(v,w),s(r,w),s(r,t)} : Set (Sym2 V)),
      e ∉ (A.append D).toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪ {s(r,v),s(v,w),s(r,w),s(r,t)}) := by
  classical
  have hrA : r ∉ A.support := fun hx ↦ hr ((Walk.mem_support_append_iff A D).mpr (Or.inl hx))
  have hrD : r ∉ D.support := fun hx ↦ hr ((Walk.mem_support_append_iff A D).mpr (Or.inr hx))
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
  have htri : ∀ e ∈ ({s(r,v),s(v,w),s(r,w)} : Set (Sym2 V)),
      e ∉ (A.append D).toSubgraph.edgeSet := by
    intro e he
    apply havoid e
    rcases he with he|he|he <;> simp_all
  have hlength : X.length+Y.length=
      ((A.append D).toSubgraph.edgeSet ∪ {s(r,v),s(v,w),s(r,w)}).ncard := by
    rw [triangle_union_ncard hrv hvw hrw _ hp htri]
    simp only [X,Y,Walk.length_cons,Walk.length_reverse,Walk.length_append]
    omega
  have hdis := disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ hcover hlength
  have hnew : s(r,t) ∉ X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet := by
    rw [hcover]
    intro he
    rcases he with he|he
    · exact havoid s(r,t) (by simp) he
    · rcases he with he|he|he
      · have he : s(r,t)=s(r,v) := he
        simp [htv,hrv.ne] at he
      · have he : s(r,t)=s(v,w) := he
        simp [hrv.ne,hrw.ne] at he
      · have he : s(r,t)=s(r,w) := he
        simp [htw,hrw.ne] at he
  have ht : t ∉ X.support ∨ t ∉ Y.support := by
    by_cases htX : t ∈ X.support
    · right
      have htA : t ∈ A.support := by
        simpa only [X,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse,
          (Ne.symm hrt.ne),false_or] using htX
      have htD : t ∉ D.support := fun htD ↦
        (hp.ne_of_mem_support_of_append htw htA htD) rfl
      simp only [Y,Walk.support_cons,List.mem_cons,not_or]
      exact ⟨hrt.ne.symm,htv,htD⟩
    · exact Or.inl htX
  have hresult := attach_common_start_edge hrt X Y hX hY hdis hnew ht
  convert hresult using 1
  rw [hcover]
  ext e
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_union]
  tauto

lemma triangle_tail_edge_absorption {r x y t a b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y) (hrt : G.Adj r t)
    (htx : t ≠ x) (hty : t ≠ y)
    (P : G.Walk a b) (hp : P.IsPath) (hr : r ∉ P.support)
    (hinter : x ∈ P.support ∨ y ∈ P.support)
    (havoid : ∀ e ∈ ({s(r,x),s(x,y),s(r,y),s(r,t)} : Set (Sym2 V)),
      e ∉ P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪ {s(r,x),s(x,y),s(r,y),s(r,t)}) := by
  have hhit : ∃ v ∈ P.support, v ∈ ({x,y} : Set V) := by
    rcases hinter with hx|hy
    · exact ⟨x,hx,by simp⟩
    · exact ⟨y,hy,by simp⟩
  obtain ⟨w,hw,A,D,hform,hD⟩ := CycleDefect.last_hit_split P {x,y} hhit
  rw [hform] at hp hr havoid ⊢
  rcases hw with hw|hw
  · have hw : w=x := hw
    subst w
    have hswap : ({s(r,y),s(y,x),s(r,x),s(r,t)} : Set (Sym2 V))=
        {s(r,x),s(x,y),s(r,y),s(r,t)} := by
      ext e
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := x)]
      tauto
    rw [←hswap] at havoid ⊢
    exact triangle_tail_edge_at_last hry hxy.symm hrx hrt hty htx A D hp hr
      (fun hy ↦ hxy.ne.symm (hD y hy (by simp))) havoid
  · have hw : w=y := hw
    subst w
    exact triangle_tail_edge_at_last hrx hxy hry hrt htx hty A D hp hr
      (fun hx ↦ hxy.ne (hD x hx (by simp))) havoid

lemma maximum_one_defect_no_two_path_cover {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) (hi : ¬(T.walk i).IsPath) :
    ¬TwoPathCover (G := G) ((T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) := by
  rintro ⟨a,b,c,d,P,Q,hP,hQ,hd,he⟩
  obtain ⟨U,hUi,hUj,hrest,_⟩ := GeneralPair.replace_two T i j hij a b c d P Q hP.isTrail hQ.isTrail hd he
  have hpU (l : Fin k) : (U.walk l).IsPath := by
    by_cases hli : l=i
    · subst l
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail i) hP hUi
    by_cases hlj : l=j
    · subst l
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail j) hQ hUj
    exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail l)
      ((T.one_defect_other_paths hs i hi).2 l hli) (hrest l hli hlj)
  have hUs := U.score_eq_edges_add_iff.mpr hpU
  have hb := hm U
  omega


omit [Fintype V] in
lemma one_edge_form {r t : V} (P : G.Walk r t) (hlen : P.length=1) :
    ∃ h : G.Adj r t, P=Walk.cons h Walk.nil := by
  cases P with
  | nil => simp at hlen
  | cons h P =>
    cases P with
    | nil => exact ⟨h,rfl⟩
    | cons g P => simp only [Walk.length_cons] at hlen; omega

lemma maximum_short_triangle_no_outside_intersection {k : ℕ} (T : TrailFamily G k)
    (r : V) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hcycle : L.cycle.length=3) (htail : L.tail.length=1)
    (j : Fin k) (hij : L.index ≠ j) (hr : r ∉ (T.walk j).support) :
    ¬∃ x ∈ L.cycle.support, x ∈ (T.walk j).support := by
  classical
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hcycle
  obtain ⟨hrt,hS⟩ := one_edge_form L.tail htail
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have htx : L.finish ≠ x := fun h ↦ hrt.ne.symm (L.inter L.finish (h.symm ▸ hxC) L.tail.end_mem_support)
  have hty : L.finish ≠ y := fun h ↦ hrt.ne.symm (L.inter L.finish (h.symm ▸ hyC) L.tail.end_mem_support)
  have he : (T.walk L.index).toSubgraph.edgeSet={s(r,x),s(x,y),s(r,y),s(r,L.finish)} := by
    rw [L.subgraph,hC,hS]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,Walk.edges_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
    tauto
  have havoid : ∀ e ∈ ({s(r,x),s(x,y),s(r,y),s(r,L.finish)} : Set (Sym2 V)),
      e ∉ (T.walk j).toSubgraph.edgeSet := by
    intro e he' hj
    exact Set.disjoint_left.mp (T.disjoint hij) (he.symm ▸ he') hj
  rintro ⟨z,hzC,hzj⟩
  have hinter : x ∈ (T.walk j).support ∨ y ∈ (T.walk j).support := by
    simp only [hC,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hzC
    rcases hzC with rfl|rfl|rfl|rfl
    · exact (hr hzj).elim
    · exact Or.inl hzj
    · exact Or.inr hzj
    · exact (hr hzj).elim
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hh := triangle_tail_edge_absorption hrx hxy hyr.symm hrt htx hty (T.walk j) hp hr hinter havoid
  apply maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  rw [he,Set.union_comm]
  exact hh

lemma cubic_quota_one_others_avoid {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hd : Nat.card (G.neighborSet r)=3) (hq : T.quota r=1)
    (j : Fin k) (hji : j ≠ L.index) : r ∉ (T.walk j).support := by
  classical
  have hcount := RootCapacity.rooted_incidence T r hs L.hasRoot r
  simp only [hd,hq,↓reduceIte,mul_one] at hcount
  have hcard : (Finset.univ.filter fun i ↦ r ∈ (T.walk i).support).card ≤ 1 := by omega
  have hri : r ∈ (T.walk L.index).support := by
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  intro hrj
  exact hji (Finset.card_le_one.mp hcard j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrj⟩)
    L.index (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hri⟩))

omit [Fintype V] in
lemma quota_one_tail_not_nil {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hq : T.quota r=1) : ¬L.tail.Nil := by
  classical
  intro hn
  have hfinish : T.finish L.index=r := L.finish_eq.trans hn.eq.symm
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin k ↦ (if T.start j=r then 1 else 0)+(if T.finish j=r then 1 else 0))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ L.index)
  rw [←quota_eq_sum_endpoints] at hh
  dsimp only at hh
  rw [L.start_eq,hfinish,hq] at hh
  norm_num at hh

/-- This excludes only the one-edge-tail case at a cubic root, not arbitrary
triangle lollipops. The global (free-quota) score maximum is essential. -/
lemma cubic_triangle_tail_length_ge_two {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hd : Nat.card (G.neighborSet r)=3) (hq : T.quota r ≤ 2) (hcycle : L.cycle.length=3) :
    2 ≤ L.tail.length := by
  have hq1 : T.quota r=1 := (QuotaParity.small_root_quota_one_iff T L.hasRoot hq).mpr (by rw [hd]; decide)
  have hnonzero : L.tail.length ≠ 0 := fun h ↦ quota_one_tail_not_nil T r L hq1 (Walk.nil_iff_length_eq.mpr h)
  by_contra hshort
  have htail : L.tail.length=1 := by omega
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hcycle
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hx2 := NormalRemainder.cycle_degree_ge_two L.cycle L.isCycle hxC
  have hx3 : 3 ≤ Nat.card (G.neighborSet x) := by
    by_contra hn
    have hxdeg : Nat.card (G.neighborSet x)=2 := by omega
    have hh := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hrx.symm hxdeg
    omega
  have hxN : x ∈ (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support := by
    by_contra hx
    have hh := TailEar.missing_normal_degree_bound T r L hs hm hx
    rw [if_neg hrx.ne.symm] at hh
    omega
  obtain ⟨z,j,hj,hxj⟩ := hxN
  have hji := (Finset.mem_erase.mp hj).1
  exact maximum_short_triangle_no_outside_intersection T r L hs hm hcycle htail j hji.symm
    (cubic_quota_one_others_avoid T r L hs hd hq1 j hji)
    ⟨x,hxC,Walk.mem_support_of_adj_toSubgraph hxj⟩

end Erdos583ShortLollipopDevelopment
