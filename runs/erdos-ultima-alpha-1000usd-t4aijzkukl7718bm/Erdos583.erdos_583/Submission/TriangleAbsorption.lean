import Submission.GeneralPair

/-! A triangle can be absorbed into an intersecting path using two paths.
This is not an unrestricted cycle/path conversion theorem. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
namespace Erdos583TriangleAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma append_cons_support_disjoint {V : Type*} {G : SimpleGraph V} {a v y b : V}
    (A : G.Walk a v) (h : G.Adj v y) (R : G.Walk y b)
    (hp : (A.append (Walk.cons h R)).IsPath) :
    ∀ x, x ∈ A.support → x ∈ R.support → False := by
  intro x hx hy
  by_cases hv : x=v
  · subst x
    exact (Walk.cons_isPath_iff h R).mp hp.of_append_right |>.2 hy
  · exact (hp.ne_of_mem_support_of_append hv hx (List.mem_cons_of_mem _ hy)) rfl

lemma disjoint_of_cover_length {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b c d : V} (P : G.Walk a b) (Q : G.Walk c d)
    (hp : P.IsTrail) (hq : Q.IsTrail) (E : Set (Sym2 V))
    (he : P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=E)
    (hn : P.length+Q.length=E.ncard) :
    Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
  have hh := Set.ncard_union_add_ncard_inter P.toSubgraph.edgeSet Q.toSubgraph.edgeSet
  rw [he,trail_edgeSet_ncard P hp,trail_edgeSet_ncard Q hq] at hh
  have hz : (P.toSubgraph.edgeSet ∩ Q.toSubgraph.edgeSet).ncard=0 := by omega
  apply Set.disjoint_iff_inter_eq_empty.mpr
  exact (Set.ncard_eq_zero (Set.toFinite _)).mp hz

/-- The three-visit case. The old path visits u before v before w. Its
v-to-w segment has a first edge v-y not belonging to the triangle. -/
lemma ordered_triangle_surgery {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v w y : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (A : G.Walk a v) (g : G.Adj v y) (Q : G.Walk y w) (D : G.Walk w b)
    (hp : (A.append (Walk.cons g (Q.append D))).IsPath)
    (hu : u ∈ A.support)
    (havoid : ∀ e ∈ ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)),
      e ∉ (A.append (Walk.cons g (Q.append D))).toSubgraph.edgeSet) :
    ∃ X : G.Walk a y, ∃ Y : G.Walk y b,
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
      X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
        (A.append (Walk.cons g (Q.append D))).toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)} := by
  classical
  let P := A.append (Walk.cons g (Q.append D))
  have hQD : (Q.append D).IsPath := hp.of_append_right.of_cons
  have hcross := append_cons_support_disjoint A g (Q.append D) hp
  have hAQ (x : V) (hx : x ∈ A.support) (hy : x ∈ Q.support) : False :=
    hcross x hx ((Q.mem_support_append_iff D).mpr (Or.inl hy))
  have hAD (x : V) (hx : x ∈ A.support) (hy : x ∈ D.support) : False :=
    hcross x hx ((Q.mem_support_append_iff D).mpr (Or.inr hy))
  have hyw : y ≠ w := by
    intro hh
    apply havoid s(v,w) (by simp)
    have he : s(v,y) ∈ (A.append (Walk.cons g (Q.append D))).toSubgraph.edgeSet := by
      simp
    simpa only [hh] using he
  have hyu : y ≠ u := fun hh ↦ hAQ u hu (hh ▸ Q.start_mem_support)
  have hyv : y ≠ v := g.ne.symm
  have hyD : y ∉ D.support := by
    intro hh
    exact (hQD.ne_of_mem_support_of_append hyw Q.start_mem_support hh) rfl
  have huD : u ∉ D.support := hAD u hu
  have hvD : v ∉ D.support := hAD v A.end_mem_support
  let X := (A.concat hvw).append Q.reverse
  let Y := Walk.cons g.symm (Walk.cons huv.symm (Walk.cons huw D))
  have hX : X.IsPath := by
    apply path_append_of_support_intersection
    · exact hp.of_append_left.concat (fun hh ↦ hAQ w hh Q.end_mem_support) hvw
    · exact hQD.of_append_left.reverse
    · intro x hx hy
      have hy' : x ∈ Q.support := by simpa using hy
      have hx' : x ∈ A.support ∨ x=w := by
        simpa only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] using hx
      exact hx'.elim (fun hh ↦ (hAQ x hh hy').elim) id
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨hQD.of_append_right,huD⟩,huv.ne.symm,hvD⟩,hyv,hyu,hyD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      P.toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)} := by
    ext e
    simp only [X,Y,P,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_append,
      Walk.edges_concat,Walk.edges_cons,Walk.edges_reverse,List.concat_eq_append,List.mem_append,
      List.mem_reverse,List.mem_cons,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y),
      Sym2.eq_swap (a := v) (b := u)]
    tauto
  have hs3 : ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)).ncard=3 := by
    have h1 : s(u,v) ≠ s(v,w) := by simp [huv.ne,hvw.ne,huw.ne]
    have h2 : s(u,v) ≠ s(u,w) := by simp [hvw.ne,huw.ne]
    have h3 : s(v,w) ≠ s(u,w) := by simp [huv.ne.symm,hvw.ne]
    simp [Set.ncard_insert_of_notMem,h1,h2,h3]
  have hdis : Disjoint P.toSubgraph.edgeSet ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)) := by
    apply Set.disjoint_left.mpr
    intro e he hf
    exact havoid e hf he
  have hn : X.length+Y.length=(P.toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}).ncard := by
    rw [Set.ncard_union_eq hdis,trail_edgeSet_ncard P hp.isTrail,hs3]
    simp only [X,Y,P,Walk.length_append,Walk.length_concat,Walk.length_reverse,Walk.length_cons]
    omega
  exact ⟨X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩


def TwoPathCover {V : Type*} {G : SimpleGraph V} (E : Set (Sym2 V)) : Prop :=
  ∃ a b c d, ∃ P : G.Walk a b, ∃ Q : G.Walk c d,
    P.IsPath ∧ Q.IsPath ∧ Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=E

lemma triangle_union_ncard {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (P : G.Walk a b) (hp : P.IsPath)
    (havoid : ∀ e ∈ ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)), e ∉ P.toSubgraph.edgeSet) :
    (P.toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}).ncard=P.length+3 := by
  have h1 : s(u,v) ≠ s(v,w) := by simp [huv.ne,hvw.ne,huw.ne]
  have h2 : s(u,v) ≠ s(u,w) := by simp [hvw.ne,huw.ne]
  have h3 : s(v,w) ≠ s(u,w) := by simp [huv.ne.symm,hvw.ne]
  have hd : Disjoint P.toSubgraph.edgeSet ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)) :=
    Set.disjoint_left.mpr (fun e he hf ↦ havoid e hf he)
  rw [Set.ncard_union_eq hd,trail_edgeSet_ncard P hp.isTrail]
  simp [Set.ncard_insert_of_notMem,h1,h2,h3]

lemma missing_triangle_surgery {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (A : G.Walk a w) (D : G.Walk w b) (hp : (A.append D).IsPath)
    (huA : u ∉ A.support) (huD : u ∉ D.support) (hvD : v ∉ D.support)
    (havoid : ∀ e ∈ ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)), e ∉ (A.append D).toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}) := by
  let X := Walk.cons huw A.reverse
  let Y := Walk.cons huv (Walk.cons hvw D)
  have hX : X.IsPath := (Walk.cons_isPath_iff huw A.reverse).mpr
    ⟨hp.of_append_left.reverse,by simpa using huA⟩
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨hp.of_append_right,hvD⟩,huv.ne,huD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (A.append D).toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)} := by
    ext e
    simp only [X,Y,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,
      Walk.edges_reverse,Walk.edges_append,List.mem_cons,List.mem_reverse,List.mem_append,
      Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hn : X.length+Y.length=((A.append D).toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}).ncard := by
    rw [triangle_union_ncard huv hvw huw _ hp havoid]
    simp only [X,Y,Walk.length_cons,Walk.length_reverse,Walk.length_append]
    omega
  exact ⟨u,a,u,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩

lemma triangle_absorb_at_last {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (A₀ : G.Walk a w) (D : G.Walk w b) (hp : (A₀.append D).IsPath)
    (hD : ∀ x ∈ D.support, x ∈ ({u,v,w} : Set V) → x=w)
    (havoid : ∀ e ∈ ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)), e ∉ (A₀.append D).toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A₀.append D).toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}) := by
  classical
  have huD : u ∉ D.support := fun hh ↦ huw.ne (hD u hh (by simp))
  have hvD : v ∉ D.support := fun hh ↦ hvw.ne (hD v hh (by simp))
  by_cases hu : u ∈ A₀.support
  · by_cases hv : v ∈ A₀.support
    · obtain ⟨z,hz,A,R,hform,hR⟩ := CycleDefect.last_hit_split A₀ ({u,v} : Set V) ⟨u,hu,by simp⟩
      have hstep {s t : V} (hst : G.Adj s t) (htw : G.Adj t w) (hsw : G.Adj s w)
          (hpair : ({s,t} : Set V)={u,v})
          (ht : z=t) (hs : s ∈ A₀.support)
          (hE : ({s(s,t),s(t,w),s(s,w)} : Set (Sym2 V))={s(u,v),s(v,w),s(u,w)}) :
          TwoPathCover (G := G) ((A₀.append D).toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}) := by
        subst z
        have hsA : s ∈ A.support := by
          have hh : s ∈ A.support ∨ s ∈ R.support := by
            rw [hform,Walk.mem_support_append_iff] at hs
            exact hs
          rcases hh with hh|hh
          · exact hh
          · have hsset : s ∈ ({u,v} : Set V) := by rw [←hpair]; simp
            exact (hst.ne (hR s hh hsset)).elim
        cases R with
        | nil => exact (htw.ne rfl).elim
        | @cons _ y _ g Q =>
          have hp' : (A.append (Walk.cons g (Q.append D))).IsPath := by
            simpa only [hform,←Walk.append_assoc,Walk.cons_append] using hp
          have hav' : ∀ e ∈ ({s(s,t),s(t,w),s(s,w)} : Set (Sym2 V)),
              e ∉ (A.append (Walk.cons g (Q.append D))).toSubgraph.edgeSet := by
            intro e he
            have hh := havoid e (hE ▸ he)
            simpa only [hform,←Walk.append_assoc,Walk.cons_append] using hh
          obtain ⟨X,Y,hX,hY,hd,he⟩ := ordered_triangle_surgery hst htw hsw A g Q D hp' hsA hav'
          refine ⟨a,y,y,b,X,Y,hX,hY,hd,?_⟩
          simpa only [hform,←Walk.append_assoc,Walk.cons_append,hE] using he
      rcases (show z=u ∨ z=v by simpa using hz) with hz|hz
      · apply hstep huv.symm huw hvw (by ext; simp [or_comm]) hz hv
        ext e
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := v) (b := u)]
        tauto
      · exact hstep huv hvw huw rfl hz hu rfl
    · have hE : ({s(v,u),s(u,w),s(v,w)} : Set (Sym2 V))={s(u,v),s(v,w),s(u,w)} := by
        ext e
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := v) (b := u)]
        tauto
      have hh := missing_triangle_surgery huv.symm huw hvw A₀ D hp hv hvD huD
        (by simpa only [hE] using havoid)
      simpa only [hE] using hh
  · exact missing_triangle_surgery huv hvw huw A₀ D hp hu huD hvD havoid

/-- An edge-disjoint triangle and an intersecting simple path have a
partition into two simple paths. No restriction on the path's length or on
its number of outside vertices is needed. -/
lemma triangle_path_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (P : G.Walk a b) (hp : P.IsPath)
    (hinter : ∃ x ∈ P.support, x ∈ ({u,v,w} : Set V))
    (havoid : ∀ e ∈ ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)), e ∉ P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}) := by
  classical
  obtain ⟨z,hz,A,D,hform,hD⟩ := CycleDefect.last_hit_split P ({u,v,w} : Set V) hinter
  have hstep {s t : V} (hst : G.Adj s t) (htz : G.Adj t z) (hsz : G.Adj s z)
      (hV : ({s,t,z} : Set V)={u,v,w})
      (hE : ({s(s,t),s(t,z),s(s,z)} : Set (Sym2 V))={s(u,v),s(v,w),s(u,w)}) :
      TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪ {s(u,v),s(v,w),s(u,w)}) := by
    have hh := triangle_absorb_at_last hst htz hsz A D (hform ▸ hp)
      (by simpa only [hV] using hD) (by simpa only [hE,←hform] using havoid)
    simpa only [hE,←hform] using hh
  rcases (show z=u ∨ z=v ∨ z=w by simpa using hz) with rfl|rfl|rfl
  · apply hstep hvw huw.symm huv.symm
    · ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
    · ext e
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := w) (b := z),
        Sym2.eq_swap (a := v) (b := z)]
      tauto
  · apply hstep huw hvw.symm huv
    · ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
    · ext e
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := w) (b := z)]
      tauto
  · exact hstep huv hvw huw rfl rfl


/-- A global incidence maximum cannot contain both a whole triangle and
an intersecting path as two distinct members. -/
lemma maximal_triangle_no_intersecting_path {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hi : (T.walk i).toSubgraph=(Walk.cons huv (Walk.cons hvw (Walk.cons huw.symm Walk.nil))).toSubgraph)
    (hj : (T.walk j).IsPath) :
    ¬∃ x ∈ (T.walk j).support, x ∈ ({u,v,w} : Set V) := by
  classical
  intro hinter
  have hetri : (T.walk i).toSubgraph.edgeSet={s(u,v),s(v,w),s(u,w)} := by
    rw [hi]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := w) (b := u)]
  have havoid : ∀ e ∈ ({s(u,v),s(v,w),s(u,w)} : Set (Sym2 V)), e ∉ (T.walk j).toSubgraph.edgeSet := by
    intro e he hj
    exact Set.disjoint_left.mp (T.disjoint hij) (hetri.symm ▸ he) hj
  obtain ⟨a,b,c,d,X,Y,hX,hY,hd,he⟩ := triangle_path_absorption huv hvw huw (T.walk j) hj hinter havoid
  have he' : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [he,hetri,Set.union_comm]
  obtain ⟨U,_,_,_,hs⟩ := Erdos583GeneralPairDevelopment.replace_two T i j hij a b c d X Y
    hX.isTrail hY.isTrail hd he'
  have hlen : X.length+Y.length=(T.walk j).length+3 := by
    have hc := triangle_union_ncard huv hvw huw (T.walk j) hj havoid
    rw [←he,Set.ncard_union_eq hd,trail_edgeSet_ncard X hX.isTrail,
      trail_edgeSet_ncard Y hY.isTrail] at hc
    exact hc
  have hi3 : (T.walk i).toSubgraph.verts.ncard=3 := by
    have hvset : (T.walk i).toSubgraph.verts=({u,v,w} : Set V) := by
      rw [hi]
      ext x
      simp only [Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_nil,List.mem_cons,
        List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    rw [hvset]
    simp [Set.ncard_insert_of_notMem,huv.ne,hvw.ne,huw.ne]
  rw [hi3,(walk_vertex_ncard_eq_iff (T.walk j)).mpr hj,
    (walk_vertex_ncard_eq_iff X).mpr hX,(walk_vertex_ncard_eq_iff Y).mpr hY] at hs
  have hb := hm U
  omega


/-- In a connected graph, a single-defect global maximum with at least two
members has no member whose whole subgraph is a triangle. -/
lemma maximal_single_defect_no_triangle {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : 2 ≤ k)
    (i : Fin k) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) :
    (T.walk i).toSubgraph ≠ (Walk.cons huv (Walk.cons hvw (Walk.cons huw.symm Walk.nil))).toSubgraph := by
  classical
  intro hi
  let S : Set V := {u,v,w}
  have hiv : (T.walk i).toSubgraph.verts=S := by
    rw [hi]
    ext x
    simp only [S,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hie : (T.walk i).toSubgraph.edgeSet={s(u,v),s(v,w),s(u,w)} := by
    rw [hi]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := w) (b := u)]
  have hiNP : ¬(T.walk i).IsPath := by
    intro hp
    have hn := (walk_vertex_ncard_eq_iff (T.walk i)).mpr hp
    rw [←trail_edgeSet_ncard (T.walk i) (T.isTrail i),hie,hiv] at hn
    have h1 : s(u,v) ≠ s(v,w) := by simp [huv.ne,hvw.ne,huw.ne]
    have h2 : s(u,v) ≠ s(u,w) := by simp [hvw.ne,huw.ne]
    have h3 : s(v,w) ≠ s(u,w) := by simp [huv.ne.symm,hvw.ne]
    simp [S,Set.ncard_insert_of_notMem,huv.ne,hvw.ne,huw.ne,h1,h2,h3] at hn
  have hother (j : Fin k) (hj : j ≠ i) : ¬∃ x ∈ (T.walk j).support, x ∈ S :=
    maximal_triangle_no_intersecting_path T hm i j hj.symm huv hvw huw hi
      ((T.one_defect_other_paths hs i hiNP).2 j hj)
  have hS : S=Set.univ := by
    apply TrailBudget.connected_closed_set hG S ⟨u,by simp [S]⟩
    intro x y hxy hx
    obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
    by_cases hji : j=i
    · subst j
      have hy : y ∈ (T.walk i).toSubgraph.verts :=
        (T.walk i).toSubgraph.edge_vert (show (T.walk i).toSubgraph.Adj y x from hj.symm)
      rwa [hiv] at hy
    · have hxj : x ∈ (T.walk j).support := (T.walk j).mem_verts_toSubgraph.mp
        ((T.walk j).toSubgraph.edge_vert (show (T.walk j).toSubgraph.Adj x y from hj))
      exact (hother j hji ⟨x,hxj,hx⟩).elim
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j,hji⟩ := exists_ne i
  exact hother j hji ⟨T.start j,(T.walk j).start_mem_support,by rw [hS]; trivial⟩

/-- The same exclusion at the Gallai budget; the three distinct triangle
vertices ensure that at least two indexed slots are available. -/
lemma budget_maximum_no_triangle {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : Fintype.card V ≤ 2*k)
    (i : Fin k) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) :
    (T.walk i).toSubgraph ≠ (Walk.cons huv (Walk.cons hvw (Walk.cons huw.symm Walk.nil))).toSubgraph := by
  classical
  have hc : 3 ≤ Fintype.card V := by
    have hh := Finset.card_le_card (show ({u,v,w} : Finset V) ⊆ Finset.univ from Finset.subset_univ _)
    simpa [huv.ne,hvw.ne,huw.ne] using hh
  exact maximal_single_defect_no_triangle T hG hs hm (by omega) i huv hvw huw

end Erdos583TriangleAbsorptionDevelopment
