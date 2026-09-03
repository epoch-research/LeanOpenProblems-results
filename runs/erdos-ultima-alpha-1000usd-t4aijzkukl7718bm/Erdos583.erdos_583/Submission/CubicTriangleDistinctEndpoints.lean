import Submission.TwoMemberExtension

/-! Restoration when the external neighbors belong to distinct endpoint paths. -/
namespace Erdos583CubicTriangleDistinctEndpointsDevelopment
open SimpleGraph Erdos583Work
open Erdos583TwoMemberExtensionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma puncture_walk_avoids_removed {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b x : V} (P : (puncture G S).Walk a b) (ha : a ∉ S) (hx : x ∈ S) : x ∉ P.support := by
  intro hm
  have hh := DegreeThreeReduction.isolated_mem_support (G := puncture G S) (u := x)
    (fun v hv ↦ hv.2.1 hx) P hm
  exact ha (hh.1 ▸ hx)

lemma cubic_triangle_distinct_endpoints_lift {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r x y a b u v : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (D : Finset (puncture G ({x,y} : Set V)).Subgraph)
    (hD : GoodDecomposition (puncture G ({x,y} : Set V)) D)
    (P : (puncture G ({x,y} : Set V)).Walk a u)
    (Q : (puncture G ({x,y} : Set V)).Walk b v)
    (hP : P.IsPath) (hQ : Q.IsPath) (hPD : P.toSubgraph ∈ D) (hQD : Q.toSubgraph ∈ D)
    (hPQ : P.toSubgraph ≠ Q.toSubgraph) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let S : Set V := {x,y}
  let H := puncture G S
  let R : G.Walk x y := Walk.cons hrx.symm (Walk.cons hry Walk.nil)
  let N : G.Walk a b := Walk.cons hxa.symm (Walk.cons hxy (Walk.cons hyb Walk.nil))
  have hR : R.IsPath := by simp [R,Walk.cons_isPath_iff,hrx.ne.symm,hxy.ne,hry.ne]
  have hGcover : G.edgeSet=(H.edgeSet ∪ N.toSubgraph.edgeSet) ∪ R.toSubgraph.edgeSet := by
    apply puncture_two_walks_cover S N R
    intro t ht z htz
    rcases ht with rfl | rfl
    · rcases hNx z htz with rfl | rfl | rfl <;> simp [N,R,Sym2.eq_swap]
    · rcases hNy z htz with rfl | rfl | rfl <;> simp [N,R,Sym2.eq_swap]
  have hRH : Disjoint R.toSubgraph.edgeSet H.edgeSet := by
    apply puncture_disjoint_walk S R
    intro e he
    have hh : e=s(x,r) ∨ e=s(r,y) := by simpa [R] using he
    rcases hh with rfl | rfl
    · exact ⟨x,Or.inl rfl,by simp⟩
    · exact ⟨y,Or.inr rfl,by simp⟩
  have hRN : Disjoint R.toSubgraph.edgeSet N.toSubgraph.edgeSet := by
    simp [Set.disjoint_left,R,N,hrx.ne,hry.ne,hxy.ne,hxy.ne.symm,
      hxa.ne,hyb.ne.symm,har.symm,hay.symm,hbr.symm,hbx.symm]
  let F := G.deleteEdges R.toSubgraph.edgeSet
  have hHF : H ≤ F := by
    intro p q hpq
    exact deleteEdges_adj.mpr ⟨(puncture_le G S) hpq,
      fun hh ↦ Set.disjoint_left.mp hRH hh hpq⟩
  have hFe : F.edgeSet=H.edgeSet ∪ N.toSubgraph.edgeSet := by
    rw [edgeSet_deleteEdges,hGcover]
    ext e
    simp only [Set.mem_diff,Set.mem_union]
    constructor
    · tauto
    · intro hh
      refine ⟨Or.inl hh,?_⟩
      intro he
      exact Set.disjoint_left.mp (disjoint_sup_right.mpr ⟨hRH,hRN⟩) he hh
  have hFedge {p q} (h : s(p,q) ∈ N.toSubgraph.edgeSet) : F.Adj p q := by
    change s(p,q) ∈ F.edgeSet
    rw [hFe]
    exact Or.inr h
  have fyx : F.Adj y x := hFedge (by simp [N,Sym2.eq_swap])
  have fxa : F.Adj x a := hFedge (by simp [N,Sym2.eq_swap])
  have fyb : F.Adj y b := hFedge (by simp [N])
  let A := Walk.cons fyx (Walk.cons fxa (P.mapLe hHF))
  let B := Walk.cons fyb (Q.mapLe hHF)
  have haS : a ∉ S := by simp [S,hxa.ne.symm,hay]
  have hbS : b ∉ S := by simp [S,hbx,hyb.ne.symm]
  have hpavoid {z} (hz : z ∈ S) : z ∉ (P.mapLe hHF).support := by
    simpa only [Walk.support_mapLe_eq_support] using puncture_walk_avoids_removed P haS hz
  have hqavoid {z} (hz : z ∈ S) : z ∉ (Q.mapLe hHF).support := by
    simpa only [Walk.support_mapLe_eq_support] using puncture_walk_avoids_removed Q hbS hz
  have hA : A.IsPath := by
    apply (Walk.cons_isPath_iff fyx _).mpr
    refine ⟨(Walk.cons_isPath_iff fxa _).mpr ⟨hP.mapLe _,hpavoid (Or.inl rfl)⟩,?_⟩
    simp only [Walk.support_cons,List.mem_cons,not_or]
    exact ⟨hxy.ne.symm,hpavoid (Or.inr rfl)⟩
  have hB : B.IsPath := (Walk.cons_isPath_iff fyb _).mpr ⟨hQ.mapLe _,hqavoid (Or.inr rfl)⟩
  let EA : Set (Sym2 V) := {s(x,y),s(x,a)}
  let EB : Set (Sym2 V) := {s(y,b)}
  have hAe : A.toSubgraph.edgeSet=P.toSubgraph.edgeSet ∪ EA := by
    ext e
    simp only [A,EA,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_mapLe_eq_edges,
      List.mem_cons,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := x)]
    tauto
  have hBe : B.toSubgraph.edgeSet=Q.toSubgraph.edgeSet ∪ EB := by
    ext e
    simp only [B,EB,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_mapLe_eq_edges,
      List.mem_cons,Set.mem_union,Set.mem_singleton_iff]
    tauto
  have haH : Disjoint EA H.edgeSet := by
    apply Set.disjoint_left.mpr
    rintro e (rfl|rfl) he <;> exact he.2.1 (Or.inl rfl)
  have hbH : Disjoint EB H.edgeSet := by
    apply Set.disjoint_left.mpr
    rintro e rfl he
    exact he.2.1 (Or.inr rfl)
  have hAB : Disjoint EA EB := by simp [EA,EB,Set.disjoint_left,hxy.ne,hbx.symm,hyb.ne,hay]
  have hcov : F.edgeSet=(H.edgeSet ∪ EA) ∪ EB := by
    rw [hFe]
    ext e
    simp only [EA,EB,N,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := a) (b := x)]
    tauto
  obtain ⟨E,hE,hEc⟩ := extend_two_members hHF D hD P.toSubgraph Q.toSubgraph hPD hQD hPQ
    A.toSubgraph B.toSubgraph ⟨_,_,A,hA,rfl⟩ ⟨_,_,B,hB,rfl⟩ EA EB hAe hBe haH hbH hAB hcov
  obtain ⟨E',hE',hE'c⟩ := restore_path_subgraph (show IsPathSubgraph R.toSubgraph from ⟨_,_,R,hR,rfl⟩) hE
  exact ⟨E',hE',by omega⟩

end Erdos583CubicTriangleDistinctEndpointsDevelopment
