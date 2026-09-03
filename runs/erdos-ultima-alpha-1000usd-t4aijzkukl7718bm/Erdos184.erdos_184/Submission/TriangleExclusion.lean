import Submission.TrianglePatterns

/-! The strong incidence-triangle obstruction for rigid cycle families. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.TriangleContacts
open CycleSegments RigidSwitching
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma no_triangle_of_cover (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    {x y z : V}
    (hx0 : x ∈ (C 0).support) (hx1 : x ∈ (C 1).support) (hx2 : x ∉ (C 2).support)
    (hy0 : y ∈ (C 0).support) (hy2 : y ∈ (C 2).support) (hy1 : y ∉ (C 1).support)
    (hz1 : z ∈ (C 1).support) (hz2 : z ∈ (C 2).support) (hz0 : z ∉ (C 0).support) : False := by
  have hnt (u) : ¬ (u ∈ (C 0).support ∧ u ∈ (C 1).support ∧ u ∈ (C 2).support) := by
    rintro ⟨hu0,hu1,hu2⟩
    exact common_vertex_impossible hrig heven (C 0) (C 1) (C 2) (hC 0) (hC 1) (hC 2)
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
      hu0 hu1 hu2 hx0 hx1 hx2 hy0 hy2 hy1 hz1 hz2 hz0
  obtain ⟨a,ha⟩ := intersection_eq_pair hrig heven (C 0) (C 1) (hC 0) (hC 1) (hd 0 1 (by decide)) hx0 hx1
  obtain ⟨b,hb⟩ := intersection_eq_pair hrig heven (C 0) (C 2) (hC 0) (hC 2) (hd 0 2 (by decide)) hy0 hy2
  obtain ⟨c,hc⟩ := intersection_eq_pair hrig heven (C 1) (C 2) (hC 1) (hC 2) (hd 1 2 (by decide)) hz1 hz2
  let p : Fin 3 → Fin 2 → V := ![![x,a],![y,b],![z,c]]
  have hp : ∀ g u, (u ∈ (C (first g)).support ∧ u ∈ (C (second g)).support) ↔ u = p g 0 ∨ u = p g 1 := by
    intro g u
    fin_cases g
    · exact ha u
    · exact hb u
    · exact hc u
  have hle := patterns_bound hrig heven root C hC hd hcover p
    (point_incidence root C p hp hnt) (point_meet root C p hp)
  have heq := IndexedCycles.number_of_cover root C hC hd hrig heven hcover
  norm_num at heq
  omega

lemma no_triangle (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    {x y z : V}
    (hx0 : x ∈ (C 0).support) (hx1 : x ∈ (C 1).support) (hx2 : x ∉ (C 2).support)
    (hy0 : y ∈ (C 0).support) (hy2 : y ∈ (C 2).support) (hy1 : y ∉ (C 1).support)
    (hz1 : z ∈ (C 1).support) (hz2 : z ∈ (C 2).support) (hz0 : z ∉ (C 0).support) : False := by
  apply no_triangle_of_cover (IndexedCycles.rigid root C hC hd hrig heven)
    (IndexedCycles.even root C hC hd) root (IndexedCycles.restrict root C)
    (IndexedCycles.restrict_cycle root C hC) (IndexedCycles.restrict_disjoint root C hd)
    (IndexedCycles.restrict_cover root C)
    (x := x) (y := y) (z := z)
  all_goals (simp only [IndexedCycles.restrict_support]; assumption)

lemma no_three_cycle_ring (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {a b c₀ x y z : V} (c : G.Walk a a) (d : G.Walk b b) (t : G.Walk c₀ c₀)
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hxc : x ∈ c.support) (hxd : x ∈ d.support) (hxt : x ∉ t.support)
    (hyc : y ∈ c.support) (hyt : y ∈ t.support) (hyd : y ∉ d.support)
    (hzd : z ∈ d.support) (hzt : z ∈ t.support) (hzc : z ∉ c.support) : False := by
  let root : Fin 3 → V := ![a,b,c₀]
  let C : ∀ k, G.Walk (root k) (root k) :=
    Fin.cases c (Fin.cases d (Fin.cases t (fun i => Fin.elim0 i)))
  have hC : ∀ k, (C k).IsCycle := by
    intro k
    fin_cases k
    · exact hc
    · exact hd
    · exact ht
  have hdis : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · exact hcd
    · exact hct
    · exact hcd.symm
    · exact (hkl rfl).elim
    · exact hdt
    · exact hct.symm
    · exact hdt.symm
    · exact (hkl rfl).elim
  exact no_triangle hrig heven root C hC hdis hxc hxd hxt hyc hyt hyd hzd hzt hzc

#print axioms no_triangle
#print axioms no_three_cycle_ring
end Erdos184Work.TriangleContacts

namespace Erdos184Work.TriangleContacts
open ChordalIncidence
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma no_subgraph_ring (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (H K L : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hL : L.coe.Connected ∧ L.coe.IsRegularOfDegree 2)
    (hHK : Disjoint H.edgeSet K.edgeSet) (hHL : Disjoint H.edgeSet L.edgeSet) (hKL : Disjoint K.edgeSet L.edgeSet)
    {x y z : V}
    (hxH : x ∈ H.verts) (hxK : x ∈ K.verts) (hxL : x ∉ L.verts)
    (hyH : y ∈ H.verts) (hyL : y ∈ L.verts) (hyK : y ∉ K.verts)
    (hzK : z ∈ K.verts) (hzL : z ∈ L.verts) (hzH : z ∉ H.verts) : False := by
  obtain ⟨c,hc,hcH⟩ := LongRing.regular_cycle_walk_at H hH.1 hH.2 x hxH
  obtain ⟨d,hd,hdK⟩ := LongRing.regular_cycle_walk_at K hK.1 hK.2 x hxK
  obtain ⟨t,ht,htL⟩ := LongRing.regular_cycle_walk_at L hL.1 hL.2 y hyL
  have sc (w) : w ∈ c.support ↔ w ∈ H.verts := by rw [← Walk.mem_verts_toSubgraph,hcH]
  have sd (w) : w ∈ d.support ↔ w ∈ K.verts := by rw [← Walk.mem_verts_toSubgraph,hdK]
  have st (w) : w ∈ t.support ↔ w ∈ L.verts := by rw [← Walk.mem_verts_toSubgraph,htL]
  have ec (e) : e ∈ c.edges ↔ e ∈ H.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hcH]
  have ed (e) : e ∈ d.edges ↔ e ∈ K.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hdK]
  have et (e) : e ∈ t.edges ↔ e ∈ L.edgeSet := by rw [← Walk.mem_edges_toSubgraph,htL]
  apply no_three_cycle_ring hrig heven c d t hc hd ht
    (List.disjoint_left.mpr (fun e he hf => Set.disjoint_left.mp hHK ((ec e).mp he) ((ed e).mp hf)))
    (List.disjoint_left.mpr (fun e he hf => Set.disjoint_left.mp hHL ((ec e).mp he) ((et e).mp hf)))
    (List.disjoint_left.mpr (fun e he hf => Set.disjoint_left.mp hKL ((ed e).mp he) ((et e).mp hf)))
    ((sc x).mpr hxH) ((sd x).mpr hxK) (fun h => hxL ((st x).mp h))
    ((sc y).mpr hyH) ((st y).mpr hyL) (fun h => hyK ((sd y).mp h))
    ((sd z).mpr hzK) ((st z).mpr hzL) (fun h => hzH ((sc z).mp h))

lemma no_incidenceTriangle (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ¬ IncidenceTriangle (pieceVertices D) := by
  rintro ⟨i,j,k,x,y,z,hxi,hyi,hzi,hyj,hzj,hxj,hzk,hxk,hyk⟩
  simp only [pieceVertices,Set.mem_toFinset] at hxi hyi hzi hyj hzj hxj hzk hxk hyk
  have hij : i.val ≠ j.val := fun h => hxj (h ▸ hxi)
  have hik : i.val ≠ k.val := fun h => hyk (h ▸ hyi)
  have hjk : j.val ≠ k.val := fun h => hxj (h.symm ▸ hxk)
  exact no_subgraph_ring hrig heven i.val j.val k.val
    (hD i.val i.property) (hD j.val j.property) (hD k.val k.property)
    (hd i.property j.property hij) (hd i.property k.property hik) (hd j.property k.property hjk)
    hyi hyj hyk hxi hxk hxj hzj hzk hzi

lemma conformal (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    Conformal (pieceVertices D) :=
  conformal_of_no_incidenceTriangle _ (no_incidenceTriangle hrig heven D hD hd)

#print axioms no_incidenceTriangle
#print axioms conformal
end Erdos184Work.TriangleContacts
