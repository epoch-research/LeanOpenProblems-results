import Submission.RootQuotaTailBound

/-! Exact two-path exchanges for a root-starting path beside a triangle and two-edge tail. -/
namespace Erdos583TriangleTailRootTemplatesDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TriangleAbsorption Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

structure Frame {V : Type*} (G : SimpleGraph V) (r x y s t : V) where
  rx : G.Adj r x
  xy : G.Adj x y
  ry : G.Adj r y
  rs : G.Adj r s
  st : G.Adj s t
  tr : t ≠ r
  sx : s ≠ x
  sy : s ≠ y
  tx : t ≠ x
  ty : t ≠ y

def Frame.edges {V : Type*} {G : SimpleGraph V} {r x y s t : V}
    (_ : Frame G r x y s t) : Set (Sym2 V) := {s(r,x),s(x,y),s(r,y),s(r,s),s(s,t)}

lemma Frame.union_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t a b : V}
    (F : Frame G r x y s t) (P : G.Walk a b) (hp : P.IsPath)
    (hd : Disjoint P.toSubgraph.edgeSet F.edges) :
    (P.toSubgraph.edgeSet ∪ F.edges).ncard=P.length+5 :=
  TriangleTailTwo.triangle_tail_union_card F.rx F.xy F.ry F.rs F.st F.tr F.sx F.sy F.tx F.ty P hp hd

lemma inner_first_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t a b : V}
    (F : Frame G r x y s t) (R : G.Walk r a) (g : G.Adj a s)
    (f : G.Adj s x) (B : G.Walk x t) (h : G.Adj t y) (D : G.Walk y b)
    (hp : (R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).IsPath)
    (har : a ≠ r)
    (hd : Disjoint (R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet F.edges) :
    TwoPathCover (G := G)
      ((R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges) := by
  let W := B.append (Walk.cons h D)
  have hW : W.IsPath := hp.of_append_right.of_cons.of_cons
  have hR := hp.of_append_left
  have hcross := append_cons_support_disjoint R g (Walk.cons f W) hp
  have hsR : s ∉ R.support := fun hh ↦ hcross s hh (by simp)
  have hxR : x ∉ R.support := fun hh ↦ hcross x hh (by simp [W])
  have htR : t ∉ R.support := fun hh ↦ hcross t hh (by simp [W])
  have hyR : y ∉ R.support := fun hh ↦ hcross y hh (by simp [W])
  have hrW : r ∉ W.support := fun hh ↦ hcross r R.start_mem_support (List.mem_cons_of_mem _ hh)
  have haW : a ∉ W.support := fun hh ↦ hcross a R.end_mem_support (List.mem_cons_of_mem _ hh)
  have hsW : s ∉ W.support := (Walk.cons_isPath_iff f W).mp hp.of_append_right.of_cons |>.2
  let X := Walk.cons F.st.symm (Walk.cons f (Walk.cons F.xy (Walk.cons F.ry.symm R)))
  let Y := Walk.cons g (Walk.cons F.rs.symm (Walk.cons F.rx W))
  have hX : X.IsPath := by
    simp only [X,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨⟨hR,hyR⟩,F.xy.ne,hxR⟩,f.ne,F.sy,hsR⟩,F.st.ne.symm,F.tx,F.ty,htR⟩
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨hW,hrW⟩,F.rs.ne.symm,hsW⟩,g.ne,har,haW⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges := by
    ext e
    simp only [X,Y,W,Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_append,
      List.mem_cons,List.mem_append,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := t) (b := s),Sym2.eq_swap (a := s) (b := r),Sym2.eq_swap (a := y) (b := r)]
    tauto
  have hl : X.length+Y.length=
      ((R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges).ncard := by
    rw [F.union_ncard _ hp hd]
    simp only [X,Y,W,Walk.length_cons,Walk.length_append]
    omega
  exact ⟨t,a,a,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hl,he⟩

lemma outer_first_long_prefix_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t a b : V}
    (F : Frame G r x y s t) (R : G.Walk r a) (g : G.Adj a t)
    (f : G.Adj t x) (B : G.Walk x s) (h : G.Adj s y) (D : G.Walk y b)
    (hp : (R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).IsPath)
    (har : a ≠ r)
    (hd : Disjoint (R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet F.edges) :
    TwoPathCover (G := G)
      ((R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges) := by
  have hBD := hp.of_append_right.of_cons.of_cons
  have hB := hBD.of_append_left
  have hD := hBD.of_append_right.of_cons
  have hR := hp.of_append_left
  have hcross := append_cons_support_disjoint R g (Walk.cons f (B.append (Walk.cons h D))) hp
  have hcBD := append_cons_support_disjoint B h D hBD
  have htR : t ∉ R.support := fun hh ↦ hcross t hh (by simp)
  have hxR : x ∉ R.support := fun hh ↦ hcross x hh (by simp)
  have hsR : s ∉ R.support := fun hh ↦ hcross s hh (by simp)
  have hyR : y ∉ R.support := fun hh ↦ hcross y hh (by simp)
  have hrB : r ∉ B.support := fun hh ↦ hcross r R.start_mem_support (by simp [hh])
  have hrD : r ∉ D.support := fun hh ↦ hcross r R.start_mem_support (by simp [hh])
  have haB : a ∉ B.support := fun hh ↦ hcross a R.end_mem_support (by simp [hh])
  have haD : a ∉ D.support := fun hh ↦ hcross a R.end_mem_support (by simp [hh])
  have htBD : t ∉ (B.append (Walk.cons h D)).support :=
    (Walk.cons_isPath_iff f _).mp hp.of_append_right.of_cons |>.2
  have htB : t ∉ B.support := fun hh ↦ htBD (by simp [hh])
  have htD : t ∉ D.support := fun hh ↦ htBD (by simp [hh])
  have hyB : y ∉ B.support := fun hh ↦ hcBD y hh D.start_mem_support
  have hxD : x ∉ D.support := fun hh ↦ hcBD x B.start_mem_support hh
  have hsD : s ∉ D.support := fun hh ↦ hcBD s B.end_mem_support hh
  let Z := B.reverse.append (Walk.cons F.rx.symm (Walk.cons F.ry D))
  have hZ : Z.IsPath := by
    apply path_append_of_support_intersection hB.reverse
      ((Walk.cons_isPath_iff _ _).mpr ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hD,hrD⟩,by
        simpa only [Walk.support_cons,List.mem_cons,not_or] using ⟨F.rx.ne.symm,hxD⟩⟩)
    intro z hzB hz
    have hzB' : z ∈ B.support := by simpa using hzB
    simp only [Walk.support_cons,List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact hz
    · exact (hrB hzB').elim
    · exact (hcBD z hzB' hz).elim
  let X := Walk.cons f (Walk.cons F.xy (Walk.cons h.symm (Walk.cons F.rs.symm R)))
  let Y := Walk.cons g (Walk.cons F.st.symm Z)
  have hX : X.IsPath := by
    simp only [X,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨⟨hR,hsR⟩,F.sy.symm,hyR⟩,F.xy.ne,F.sx.symm,hxR⟩,F.tx,F.ty,F.st.ne.symm,htR⟩
  have htZ : t ∉ Z.support := by
    simp only [Z,Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse,
      Walk.support_cons,List.mem_cons,not_or]
    exact ⟨htB,F.tx,F.tr,htD⟩
  have haZ : a ∉ Z.support := by
    simp only [Z,Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse,
      Walk.support_cons,List.mem_cons,not_or]
    exact ⟨haB,fun he ↦ haB (he ▸ B.start_mem_support),har,haD⟩
  have hY : Y.IsPath := (Walk.cons_isPath_iff _ _).mpr
    ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hZ,htZ⟩,by
      simpa only [Walk.support_cons,List.mem_cons,not_or] using ⟨g.ne,haZ⟩⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges := by
    ext e
    simp only [X,Y,Z,Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_append,
      Walk.edges_reverse,List.mem_reverse,List.mem_cons,List.mem_append,Set.mem_union,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := t) (b := s),
      Sym2.eq_swap (a := s) (b := r),Sym2.eq_swap (a := x) (b := r),Sym2.eq_swap (a := y) (b := s)]
    tauto
  have hl : X.length+Y.length=
      ((R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges).ncard := by
    rw [F.union_ncard _ hp hd]
    simp only [X,Y,Z,Walk.length_cons,Walk.length_append,Walk.length_reverse]
    omega
  exact ⟨t,a,a,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hl,he⟩

lemma outer_first_long_middle_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t a b : V}
    (F : Frame G r x y s t) (e : G.Adj r t) (f : G.Adj t x)
    (R : G.Walk x a) (g : G.Adj a s) (h : G.Adj s y) (D : G.Walk y b)
    (hp : (Walk.cons e (Walk.cons f (R.append (Walk.cons g (Walk.cons h D))))).IsPath)
    (hax : a ≠ x)
    (hd : Disjoint (Walk.cons e (Walk.cons f (R.append (Walk.cons g (Walk.cons h D))))).toSubgraph.edgeSet F.edges) :
    TwoPathCover (G := G)
      ((Walk.cons e (Walk.cons f (R.append (Walk.cons g (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges) := by
  have hRD := hp.of_cons.of_cons
  have hR := hRD.of_append_left
  have hD := hRD.of_append_right.of_cons.of_cons
  have hc := append_cons_support_disjoint R g (Walk.cons h D) hRD
  have hrRD : r ∉ (Walk.cons f (R.append (Walk.cons g (Walk.cons h D)))).support :=
    (Walk.cons_isPath_iff e _).mp hp |>.2
  have htRD : t ∉ (R.append (Walk.cons g (Walk.cons h D))).support :=
    (Walk.cons_isPath_iff f _).mp hp.of_cons |>.2
  have hrR : r ∉ R.support := fun hh ↦ hrRD (by simp [hh])
  have htR : t ∉ R.support := fun hh ↦ htRD (by simp [hh])
  have hsR : s ∉ R.support := fun hh ↦ hc s hh (by simp)
  have hyR : y ∉ R.support := fun hh ↦ hc y hh (by simp)
  have hrD : r ∉ D.support := fun hh ↦ hrRD (by simp [hh])
  have htD : t ∉ D.support := fun hh ↦ htRD (by simp [hh])
  have hsD : s ∉ D.support := (Walk.cons_isPath_iff h D).mp hRD.of_append_right.of_cons |>.2
  have hxD : x ∉ D.support := fun hh ↦ hc x R.start_mem_support (by simp [hh])
  have har : a ≠ r := fun he ↦ hrR (he ▸ R.end_mem_support)
  have hat : a ≠ t := fun he ↦ htR (he ▸ R.end_mem_support)
  have hay : a ≠ y := fun he ↦ hyR (he ▸ R.end_mem_support)
  let X := Walk.cons g (Walk.cons F.rs.symm (Walk.cons F.ry (Walk.cons F.xy.symm (Walk.cons f.symm Walk.nil))))
  let Y := R.reverse.append (Walk.cons F.rx.symm (Walk.cons e (Walk.cons F.st.symm (Walk.cons h D))))
  have hX : X.IsPath := by
    simp only [X,Walk.cons_isPath_iff,Walk.support_cons,Walk.support_nil,List.mem_cons,
      List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨⟨⟨Walk.IsPath.nil,F.tx.symm⟩,F.xy.ne.symm,F.ty.symm⟩,F.ry.ne,F.rx.ne,F.tr.symm⟩,
      F.rs.ne.symm,F.sy,F.sx,F.st.ne⟩,g.ne,har,hay,hax,hat⟩
  have hY : Y.IsPath := by
    apply path_append_of_support_intersection hR.reverse
    · simp only [Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
      exact ⟨⟨⟨⟨hD,hsD⟩,F.st.ne.symm,htD⟩,e.ne,F.rs.ne,hrD⟩,
        F.rx.ne.symm,F.tx.symm,F.sx.symm,hxD⟩
    · intro z hzR hz
      have hzR' : z ∈ R.support := by simpa using hzR
      simp only [Walk.support_cons,List.mem_cons] at hz
      rcases hz with hz | rfl | rfl | rfl | hz
      · exact hz
      · exact (hrR hzR').elim
      · exact (htR hzR').elim
      · exact (hsR hzR').elim
      · exact (hc z hzR' (by simp [hz])).elim
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (Walk.cons e (Walk.cons f (R.append (Walk.cons g (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges := by
    ext q
    simp only [X,Y,Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_append,Walk.edges_nil,
      Walk.edges_reverse,List.mem_reverse,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
      Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := s) (b := r),
      Sym2.eq_swap (a := x) (b := r),Sym2.eq_swap (a := y) (b := x),Sym2.eq_swap (a := x) (b := t),Sym2.eq_swap (a := t) (b := s)]
    tauto
  have hl : X.length+Y.length=
      ((Walk.cons e (Walk.cons f (R.append (Walk.cons g (Walk.cons h D))))).toSubgraph.edgeSet ∪ F.edges).ncard := by
    rw [F.union_ncard _ hp hd]
    simp only [X,Y,Walk.length_cons,Walk.length_append,Walk.length_reverse,Walk.length_nil]
    omega
  exact ⟨a,t,a,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hl,he⟩

end Erdos583TriangleTailRootTemplatesDevelopment
