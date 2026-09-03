import Submission.MaximumCoreFamilies

/-! Alternating contacts forced by maximum, rather than rigid,
three-cycle partitions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MaximumCoreFamilies
open MaximumCycles RigidSwitching
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma indexed_maximum_of_bound {I : Type*} [Fintype I]
    (root : I → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle) (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges)
    (hbound : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → E.card ≤ Fintype.card I) :
    IsMaximum G (IndexedCycles.image root C) := by
  refine ⟨IndexedCycles.regular root C hC,⟨IndexedCycles.disjoint root C hd,?_⟩,?_⟩
  · rw [← subfamilyGraph_edges]
    apply congrArg SimpleGraph.edgeSet
    apply le_antisymm (subfamilyGraph_le _)
    intro x y hxy
    exact (IndexedCycles.edges root C s(x,y)).mpr (hcover x y hxy)
  · intro E hE hdE
    rw [IndexedCycles.card root C hC hd]
    exact hbound E hE hdE

lemma IsMaximum.no_three_common_vertices {D : Finset G.Subgraph} (hD : IsMaximum G D)
    {a b : V} (p : G.Walk a a) (q : G.Walk b b) (hp : p.IsCycle)
    (hpD : p.toSubgraph ∈ D) (hqD : q.toSubgraph ∈ D)
    (hd : p.edges.Disjoint q.edges)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxp : x ∈ p.support) (hyp : y ∈ p.support) (hzp : z ∈ p.support)
    (hxq : x ∈ q.support) (hyq : y ∈ q.support) (hzq : z ∈ q.support) : False := by
  have hne : p.toSubgraph ≠ q.toSubgraph := by
    intro he
    have heP : s(a,p.snd) ∈ p.toSubgraph.edgeSet := p.toSubgraph_adj_snd hp.not_nil
    have heQ : s(a,p.snd) ∈ q.toSubgraph.edgeSet := he ▸ heP
    exact List.disjoint_left.mp hd (p.mem_edges_toSubgraph.mp heP) (q.mem_edges_toSubgraph.mp heQ)
  have hi := maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _ hpD hqD hne
  have hs : ({x,y,z} : Set V) ⊆ p.toSubgraph.verts ∩ q.toSubgraph.verts := by
    intro w hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨p.mem_verts_toSubgraph.mpr hxp,q.mem_verts_toSubgraph.mpr hxq⟩
    · exact ⟨p.mem_verts_toSubgraph.mpr hyp,q.mem_verts_toSubgraph.mpr hyq⟩
    · exact ⟨p.mem_verts_toSubgraph.mpr hzp,q.mem_verts_toSubgraph.mpr hzq⟩
  have hlo := Set.ncard_le_ncard hs
  have hc : ({x,y,z} : Set V).ncard = 3 := by simp [hxy,hxz,hyz]
  omega

lemma maximum_arc_contact_subsingleton
    (hbound : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → E.card ≤ 3)
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v) (hvd : v ∈ d.support)
    (P : CyclePaths c v)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    (hcover : ∀ x y, G.Adj x y → s(x,y) ∈ c.edges ∨ s(x,y) ∈ d.edges ∨ s(x,y) ∈ t.edges) :
    ({x | x ∈ P.left.support ∧ x ∈ t.support} : Set V).Subsingleton := by
  obtain ⟨y,hyd,hyt⟩ := hmeet
  obtain ⟨Q⟩ := exists_cyclePaths d hd hvd huv
  obtain ⟨Q,hyQ⟩ := Q.exists_left_through hyd
  obtain ⟨hr,hs,hrs,hcov⟩ := switch_cyclePaths huv P Q hcd hinter
  let r := P.left.append Q.left.reverse
  let s := P.right.append Q.right.reverse
  have hrt : r.edges.Disjoint t.edges := by
    apply List.disjoint_left.mpr
    intro e her het
    rcases (hcov e).mp (Or.inl her) with hec | hed
    · exact List.disjoint_left.mp hct hec het
    · exact List.disjoint_left.mp hdt hed het
  have hst : s.edges.Disjoint t.edges := by
    apply List.disjoint_left.mpr
    intro e hes het
    rcases (hcov e).mp (Or.inr hes) with hec | hed
    · exact List.disjoint_left.mp hct hec het
    · exact List.disjoint_left.mp hdt hed het
  let root : Fin 3 → V := ![u,u,w]
  let C : ∀ i, G.Walk (root i) (root i) :=
    Fin.cases r (Fin.cases s (Fin.cases t (fun i => Fin.elim0 i)))
  have hC (i : Fin 3) : (C i).IsCycle := by
    fin_cases i
    · exact hr
    · exact hs
    · exact ht
  have hdis : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hrs
    · exact hrt
    · exact hrs.symm
    · exact (hij rfl).elim
    · exact hst
    · exact hrt.symm
    · exact hst.symm
    · exact (hij rfl).elim
  have hcovC : ∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges := by
    intro x y hxy
    rcases hcover x y hxy with he | he | he
    · rcases (hcov s(x,y)).mpr (Or.inl he) with he | he
      · exact ⟨0,he⟩
      · exact ⟨1,he⟩
    · rcases (hcov s(x,y)).mpr (Or.inr he) with he | he
      · exact ⟨0,he⟩
      · exact ⟨1,he⟩
    · exact ⟨2,he⟩
  have hm := indexed_maximum_of_bound root C hC hdis hcovC (by simpa using hbound)
  have hdist (x : V) (hxc : x ∈ c.support) (hxt : x ∈ t.support) : x ≠ y := by
    intro he
    have hxd : x ∈ d.support := he.symm ▸ hyd
    rcases hinter x hxc hxd with he | he
    · exact hut (he ▸ hxt)
    · exact hvt (he ▸ hxt)
  intro x hx z hz
  by_contra hxz
  have hxr : x ∈ r.support := (Walk.mem_support_append_iff _ _).mpr (Or.inl hx.1)
  have hzr : z ∈ r.support := (Walk.mem_support_append_iff _ _).mpr (Or.inl hz.1)
  have hyr : y ∈ r.support := (Walk.mem_support_append_iff _ _).mpr (Or.inr (by simpa using hyQ))
  exact hm.no_three_common_vertices r t hr
    (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
    (Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩) hrt hxz
    (hdist x (P.left_support_subset hx.1) hx.2) (hdist z (P.left_support_subset hz.1) hz.2)
    hxr hzr hyr hx.2 hz.2 hyt

lemma maximum_contacts_alternate
    (hbound : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → E.card ≤ 3)
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v) (hvd : v ∈ d.support)
    (P : CyclePaths c v)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    (hcover : ∀ x y, G.Adj x y → s(x,y) ∈ c.edges ∨ s(x,y) ∈ d.edges ∨ s(x,y) ∈ t.edges)
    {x z : V} (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    (x ∈ P.left.support ∧ z ∈ P.right.support) ∨
      (z ∈ P.left.support ∧ x ∈ P.right.support) := by
  have hl := maximum_arc_contact_subsingleton hbound hd ht huv hvd P hcd hct hdt hinter hut hvt hmeet hcover
  have hr := maximum_arc_contact_subsingleton hbound hd ht huv hvd P.swap hcd hct hdt hinter hut hvt hmeet hcover
  rcases (P.support_cover x).mpr hxc with hx | hx <;>
    rcases (P.support_cover z).mpr hzc with hz | hz
  · exact (hxz (hl ⟨hx,hxt⟩ ⟨hz,hzt⟩)).elim
  · exact Or.inl ⟨hx,hz⟩
  · exact Or.inr ⟨hz,hx⟩
  · exact (hxz (hr ⟨hx,hxt⟩ ⟨hz,hzt⟩)).elim

#print axioms maximum_contacts_alternate
end Erdos184Work.MaximumCoreFamilies
