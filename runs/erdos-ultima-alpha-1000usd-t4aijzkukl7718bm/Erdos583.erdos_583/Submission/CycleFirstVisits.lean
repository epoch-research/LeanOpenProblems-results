import Submission.Work

/-! An unrestricted cycle length is allowed when the path's first two
cycle visits are joined by a cycle edge. -/
namespace Erdos583CycleFirstVisitsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.TriangleAbsorption
open scoped Classical
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
/-- A cycle may be oriented and based so that any chosen edge is its first edge. -/
lemma cycle_edge_first {r u v : V} (C : G.Walk r r) (hc : C.IsCycle)
    (huv : G.Adj u v) (he : s(u,v) ∈ C.edges) :
    ∃ Q : G.Walk v u, (Walk.cons huv Q).IsCycle ∧
      (Walk.cons huv Q).toSubgraph=C.toSubgraph := by
  classical
  have hu : u ∈ C.support := C.fst_mem_support_of_mem_edges he
  let D := C.rotate hu
  have hD : D.IsCycle := hc.rotate hu
  have hDC : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hu
  have heD : s(u,v) ∈ D.edges := by
    rw [←Walk.mem_edges_toSubgraph,hDC,Walk.mem_edges_toSubgraph]
    exact he
  cases hform : D with
  | nil => exact (hD.not_nil (hform ▸ Walk.Nil.nil)).elim
  | @cons _ x _ h R =>
    have hc' : (Walk.cons h R).IsCycle := hform ▸ hD
    have hsub : (Walk.cons h R).toSubgraph=C.toSubgraph := hform ▸ hDC
    by_cases hxv : x=v
    · subst x
      exact ⟨R,hc',hsub⟩
    · have hRv : s(u,v) ∈ R.edges := by
        rw [hform,Walk.edges_cons,List.mem_cons] at heD
        rcases heD with hh|hh
        · rcases Sym2.eq_iff.mp hh with ⟨_,hvx⟩|⟨hux,_⟩
          · exact (hxv hvx.symm).elim
          · exact (h.ne hux).elim
        · exact hh
      have hRp := (Walk.cons_isCycle_iff R h).mp hc' |>.1
      have hRv' : s(u,v) ∈ R.reverse.edges := by simpa using hRv
      have hvfirst := hRp.reverse.eq_snd_of_mem_edges hRv'
      cases hf : R.reverse with
      | nil => simp only [hf,Walk.edges_nil,List.not_mem_nil] at hRv'
      | @cons _ w _ h' S =>
        have hvw : v=w := by simpa only [hf,Walk.snd_cons] using hvfirst
        subst w
        refine ⟨S.concat h.symm,?_,?_⟩
        · have hh := hc'.reverse
          simpa only [Walk.reverse_cons,hf,Walk.cons_append,Walk.concat_eq_append] using hh
        · have hh : (Walk.cons h R).reverse.toSubgraph=C.toSubgraph := by
            rw [Walk.toSubgraph_reverse,hsub]
          simpa only [Walk.reverse_cons,hf,Walk.cons_append,Walk.concat_eq_append] using hh

/-- Traverse the rest of the cycle backwards, return along the old path's
first excursion, and put the removed excursion edge at the other new path's
start. The freshness assumptions say these are the first two cycle visits. -/
lemma adjacent_first_surgery {a b u v x : V} (huv : G.Adj u v)
    (Q : G.Walk v u) (hc : (Walk.cons huv Q).IsCycle)
    (A : G.Walk a u) (h : G.Adj u x) (R : G.Walk x v) (D : G.Walk v b)
    (hp : (A.append (Walk.cons h (R.append D))).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ Q.support → z=u)
    (hR : ∀ z ∈ R.support, z ∈ Q.support → z=v)
    (hd : Disjoint (A.append (Walk.cons h (R.append D))).toSubgraph.edgeSet
      (Walk.cons huv Q).toSubgraph.edgeSet) :
    ∃ X : G.Walk a x, ∃ Y : G.Walk x b, X.IsPath ∧ Y.IsPath ∧
      Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
      X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
        (A.append (Walk.cons h (R.append D))).toSubgraph.edgeSet ∪
          (Walk.cons huv Q).toSubgraph.edgeSet := by
  classical
  let P := A.append (Walk.cons h (R.append D))
  have hQ : Q.IsPath := (Walk.cons_isCycle_iff Q huv).mp hc |>.1
  have hRD := hp.of_append_right.of_cons
  have hcross := append_cons_support_disjoint A h (R.append D) hp
  have hAR (z : V) (hzA : z ∈ A.support) (hzR : z ∈ R.support) : False :=
    hcross z hzA ((R.mem_support_append_iff D).mpr (Or.inl hzR))
  have hAD (z : V) (hzA : z ∈ A.support) (hzD : z ∈ D.support) : False :=
    hcross z hzA ((R.mem_support_append_iff D).mpr (Or.inr hzD))
  have hxv : x ≠ v := by
    intro he
    apply Set.disjoint_left.mp hd (show s(u,x) ∈ P.toSubgraph.edgeSet by simp [P])
    simp [he]
  have hxD : x ∉ D.support := fun hz ↦
    (hRD.ne_of_mem_support_of_append hxv R.start_mem_support hz) rfl
  have huD : u ∉ D.support := hAD u A.end_mem_support
  let L := A.append Q.reverse
  let X := L.append R.reverse
  let Y := Walk.cons h.symm (Walk.cons huv D)
  have hL : L.IsPath := by
    apply path_append_of_support_intersection hp.of_append_left hQ.reverse
    intro z hzA hzQ
    exact hA z hzA (by simpa using hzQ)
  have hX : X.IsPath := by
    apply path_append_of_support_intersection hL hRD.of_append_left.reverse
    intro z hzL hzR
    have hzR' : z ∈ R.support := by simpa using hzR
    rcases (A.mem_support_append_iff Q.reverse).mp hzL with hzA|hzQ
    · exact (hAR z hzA hzR').elim
    · exact hR z hzR' (by simpa using hzQ)
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨hRD.of_append_right,huD⟩,h.ne.symm,hxD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      P.toSubgraph.edgeSet ∪ (Walk.cons huv Q).toSubgraph.edgeSet := by
    ext e
    simp only [X,Y,L,P,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,
      Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_cons,List.mem_reverse,
      Sym2.eq_swap (a := x) (b := u)]
    tauto
  have hn : X.length+Y.length=(P.toSubgraph.edgeSet ∪ (Walk.cons huv Q).toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq hd,trail_edgeSet_ncard P hp.isTrail,trail_edgeSet_ncard _ hc.isTrail]
    simp only [X,Y,L,P,Walk.length_append,Walk.length_cons,Walk.length_reverse]
    omega
  exact ⟨X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩

/-- The unexpanded excursion version; it cannot be the cycle's own edge,
so its first edge splits off a genuinely fresh endpoint. -/
lemma adjacent_first_absorption {a b u v : V} (huv : G.Adj u v)
    (Q : G.Walk v u) (hc : (Walk.cons huv Q).IsCycle)
    (A : G.Walk a u) (B : G.Walk u v) (D : G.Walk v b)
    (hp : (A.append (B.append D)).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ Q.support → z=u)
    (hB : ∀ z ∈ B.support, z ∈ Q.support → z=u ∨ z=v)
    (hd : Disjoint (A.append (B.append D)).toSubgraph.edgeSet
      (Walk.cons huv Q).toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A.append (B.append D)).toSubgraph.edgeSet ∪
      (Walk.cons huv Q).toSubgraph.edgeSet) := by
  cases B with
  | nil => exact (huv.ne rfl).elim
  | @cons _ x _ h R =>
    have hp' : (A.append (Walk.cons h (R.append D))).IsPath := by
      simpa only [Walk.cons_append] using hp
    have hR (z : V) (hzR : z ∈ R.support) (hzQ : z ∈ Q.support) : z=v := by
      rcases hB z (List.mem_cons_of_mem _ hzR) hzQ with hzu|hzv
      · subst z
        exact ((Walk.cons_isPath_iff h (R.append D)).mp hp'.of_append_right |>.2
          ((R.mem_support_append_iff D).mpr (Or.inl hzR))).elim
      · exact hzv
    obtain ⟨X,Y,hX,hY,hd',he⟩ := adjacent_first_surgery huv Q hc A h R D hp' hA hR
      (by simpa only [Walk.cons_append] using hd)
    exact ⟨a,x,x,b,X,Y,hX,hY,hd',by simpa only [Walk.cons_append] using he⟩

/-- At the first cycle visit, an unvisited cycle neighbor permits a simpler
exchange that does not need a second visit. -/
lemma missing_first_neighbor {a b u v : V} (huv : G.Adj u v)
    (Q : G.Walk v u) (hc : (Walk.cons huv Q).IsCycle)
    (A : G.Walk a u) (D : G.Walk u b) (hp : (A.append D).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ Q.support → z=u) (hvD : v ∉ D.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet (Walk.cons huv Q).toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪ (Walk.cons huv Q).toSubgraph.edgeSet) := by
  let X := A.append Q.reverse
  let Y := Walk.cons huv.symm D
  have hQ := (Walk.cons_isCycle_iff Q huv).mp hc |>.1
  have hX : X.IsPath := by
    apply path_append_of_support_intersection hp.of_append_left hQ.reverse
    intro z hzA hzQ
    exact hA z hzA (by simpa using hzQ)
  have hY : Y.IsPath := (Walk.cons_isPath_iff huv.symm D).mpr ⟨hp.of_append_right,hvD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (A.append D).toSubgraph.edgeSet ∪ (Walk.cons huv Q).toSubgraph.edgeSet := by
    ext e
    simp only [X,Y,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_append,
      Walk.edges_reverse,List.mem_append,List.mem_cons,List.mem_reverse,Sym2.eq_swap (a := v) (b := u)]
    tauto
  have hn : X.length+Y.length=((A.append D).toSubgraph.edgeSet ∪ (Walk.cons huv Q).toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq hd,trail_edgeSet_ncard _ hp.isTrail,trail_edgeSet_ncard _ hc.isTrail]
    simp only [X,Y,Walk.length_append,Walk.length_cons,Walk.length_reverse]
    omega
  exact ⟨a,v,v,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩

lemma cycle_adjacent_first_absorption {a b r u v : V} (C : G.Walk r r) (hc : C.IsCycle)
    (A : G.Walk a u) (B : G.Walk u v) (D : G.Walk v b)
    (hp : (A.append (B.append D)).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ C.support → z=u)
    (hB : ∀ z ∈ B.support, z ∈ C.support → z=u ∨ z=v)
    (huv : C.toSubgraph.Adj u v)
    (hd : Disjoint (A.append (B.append D)).toSubgraph.edgeSet C.toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A.append (B.append D)).toSubgraph.edgeSet ∪ C.toSubgraph.edgeSet) := by
  obtain ⟨Q,hQ,hQC⟩ := cycle_edge_first C hc (C.toSubgraph.adj_sub huv) (C.mem_edges_toSubgraph.mp huv)
  have hsub {z : V} (hz : z ∈ Q.support) : z ∈ C.support := by
    rw [←Walk.mem_verts_toSubgraph,←hQC,Walk.mem_verts_toSubgraph,Walk.support_cons]
    exact List.mem_cons_of_mem _ hz
  have hh := adjacent_first_absorption (C.toSubgraph.adj_sub huv) Q hQ A B D hp
    (fun z hzA hzQ ↦ hA z hzA (hsub hzQ)) (fun z hzB hzQ ↦ hB z hzB (hsub hzQ))
    (by rw [hQC]; exact hd)
  simpa only [hQC] using hh

lemma cycle_missing_first_neighbor {a b r u v : V} (C : G.Walk r r) (hc : C.IsCycle)
    (A : G.Walk a u) (D : G.Walk u b) (hp : (A.append D).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ C.support → z=u)
    (huv : C.toSubgraph.Adj u v) (hvD : v ∉ D.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet C.toSubgraph.edgeSet) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪ C.toSubgraph.edgeSet) := by
  obtain ⟨Q,hQ,hQC⟩ := cycle_edge_first C hc (C.toSubgraph.adj_sub huv) (C.mem_edges_toSubgraph.mp huv)
  have hsub {z : V} (hz : z ∈ Q.support) : z ∈ C.support := by
    rw [←Walk.mem_verts_toSubgraph,←hQC,Walk.mem_verts_toSubgraph,Walk.support_cons]
    exact List.mem_cons_of_mem _ hz
  have hh := missing_first_neighbor (C.toSubgraph.adj_sub huv) Q hQ A D hp
    (fun z hzA hzQ ↦ hA z hzA (hsub hzQ)) hvD (by rw [hQC]; exact hd)
  simpa only [hQC] using hh

/-- In a score-maximum family, the first two visits of another path to a
whole cycle cannot be adjacent along that cycle. -/
lemma maximal_first_visits_not_adjacent {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r u v : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath)
    (A : G.Walk (T.start j) u) (B : G.Walk u v) (D : G.Walk v (T.finish j))
    (hform : T.walk j=A.append (B.append D))
    (hA : ∀ z ∈ A.support, z ∈ C.support → z=u)
    (hB : ∀ z ∈ B.support, z ∈ C.support → z=u ∨ z=v) :
    ¬C.toSubgraph.Adj u v := by
  intro huv
  apply PentagonIntersection.maximal_cycle_not_absorbable T hm i j hij C hc hi hj
  have hh := cycle_adjacent_first_absorption C hc A B D (hform ▸ hj) hA hB huv (by
    rw [←hform,←hi]; exact T.disjoint hij.symm)
  simpa only [←hform,Set.union_comm] using hh

/-- Both cycle neighbors of the first visit must occur later in the path. -/
lemma maximal_first_visit_neighbors_present {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r u v : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath)
    (A : G.Walk (T.start j) u) (D : G.Walk u (T.finish j))
    (hform : T.walk j=A.append D)
    (hA : ∀ z ∈ A.support, z ∈ C.support → z=u) (huv : C.toSubgraph.Adj u v) :
    v ∈ D.support := by
  by_contra hvD
  apply PentagonIntersection.maximal_cycle_not_absorbable T hm i j hij C hc hi hj
  have hh := cycle_missing_first_neighbor C hc A D (hform ▸ hj) hA huv hvD (by
    rw [←hform,←hi]; exact T.disjoint hij.symm)
  simpa only [←hform,Set.union_comm] using hh

end Erdos583CycleFirstVisitsDevelopment
