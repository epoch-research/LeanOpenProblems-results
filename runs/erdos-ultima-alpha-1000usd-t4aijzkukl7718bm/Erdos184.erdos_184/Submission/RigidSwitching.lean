import Submission.ThreeCycleKernels

/-! Exact two-cycle switches and their constraints in rigid even graphs.
The minimal-core rigidity implication is not assumed or proved here. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.RigidSwitching
open Critical EvenCore MaximumCycles Rigidity
set_option maxHeartbeats 1500000

variable {V : Type*} {G : SimpleGraph V}

lemma rigid_subfamily_number [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    number (subfamilyGraph D) = D.card := by
  have hlo := card_le_number_of_hereditary_minimal
    ((rigid_iff_hereditarily_evenMinimal heven).mp hrig) D hD hpD
  have hcover := (subfamilyGraph_edges D).symm
  have hlow := Subfamilies.lowerFamily_property IsCycleOrEdge D hcover
    (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD H hH))
  have hdec := Subfamilies.lowerFamily_decomposition D hcover hpD
  have hhi := number_le (Subfamilies.lowerFamily D hcover) hlow hdec
  rw [Subfamilies.lowerFamily_card] at hhi
  exact le_antisymm hhi hlo

lemma rigid_subfamily [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    CycleRigid (subfamilyGraph D) := by
  have he := cycle_subfamily_even D hD hpD
  apply hrig.mono heven (subfamilyGraph_le D)
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he v

lemma rigid_pair_intersection_le_two [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    (H K : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) : (H.verts ∩ K.verts).ncard ≤ 2 := by
  have hHK : H ≠ K := by
    intro heq
    obtain ⟨e,he⟩ := cycle_piece_edgeSet_nonempty H hH
    exact Set.disjoint_left.mp hd he (heq ▸ he)
  let D : Finset G.Subgraph := {H,K}
  have hD : ∀ L ∈ D, L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl
    · exact hH
    · exact hK
  have hpD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun L => L.edgeSet) := by
    intro A hA B hB hne
    simp only [D,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hne rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hne rfl).elim
  have hnum := rigid_subfamily_number hrig heven D hD hpD
  have hrigR := rigid_subfamily hrig heven D hD hpD
  have hR : subfamilyGraph D = H.spanningCoe ⊔ K.spanningCoe := by simp [subfamilyGraph,D]
  rw [hR] at hnum hrigR
  have hcard : D.card = 2 := by simp [D,hHK]
  by_contra! hbig
  obtain ⟨E,hE,hdE,hcE⟩ := two_cycles_exchange H K hH hK hd (by omega)
  have he := hrigR E
  simp only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at he hE
  have he := he hE hdE
  omega

lemma support_inter_of_append_isCycle {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (hc : (p.append q).IsCycle) (x : V) (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    x = u ∨ x = v := by
  have hn := hc.support_nodup
  rw [Walk.tail_support_append,List.nodup_append] at hn
  by_contra hx
  have hxu : x ≠ u := fun h => hx (Or.inl h)
  have hxv : x ≠ v := fun h => hx (Or.inr h)
  have hp : x ∈ p.support.tail := by
    rw [p.support_eq_cons,List.mem_cons] at hxp
    exact hxp.resolve_left hxu
  have hq : x ∈ q.support.tail := by
    rw [q.support_eq_cons,List.mem_cons] at hxq
    exact hxq.resolve_left hxv
  exact hn.2.2 x hp x hq rfl

/-- Two internally disjoint paths obtained by cutting a cycle at distinct vertices. -/
structure CyclePaths {u : V} (c : G.Walk u u) (v : V) where
  left : G.Walk u v
  right : G.Walk u v
  left_path : left.IsPath
  right_path : right.IsPath
  edges_disjoint : left.edges.Disjoint right.edges
  edges_cover : ∀ e, (e ∈ left.edges ∨ e ∈ right.edges) ↔ e ∈ c.edges
  support_cover : ∀ x, (x ∈ left.support ∨ x ∈ right.support) ↔ x ∈ c.support
  support_inter : ∀ x, x ∈ left.support → x ∈ right.support → x = u ∨ x = v

lemma exists_cyclePaths {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) : Nonempty (CyclePaths c v) := by
  classical
  let p := c.takeUntil v hv
  let q := (c.dropUntil v hv).reverse
  have heq : p.append q.reverse = c := by simp [p,q,Walk.take_spec]
  refine ⟨⟨p,q,hc.isPath_takeUntil hv,(cycle_dropUntil_isPath hc hv huv).reverse,?_,?_,?_,?_⟩⟩
  · simpa only [p,q,Walk.edges_reverse,List.disjoint_reverse_right] using
      hc.isTrail.disjoint_edges_takeUntil_dropUntil hv
  · intro e
    calc
      _ ↔ e ∈ (p.append q.reverse).edges := by
        simp only [Walk.edges_append,List.mem_append,Walk.edges_reverse,List.mem_reverse]
      _ ↔ e ∈ c.edges := by rw [heq]
  · intro x
    calc
      _ ↔ x ∈ (p.append q.reverse).support := by
        simp only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse]
      _ ↔ x ∈ c.support := by rw [heq]
  · intro x hxp hxq
    apply support_inter_of_append_isCycle (heq ▸ hc) x hxp
    simpa only [Walk.support_reverse,List.mem_reverse] using hxq

namespace CyclePaths
variable {u v : V} {c : G.Walk u u}

def swap (P : CyclePaths c v) : CyclePaths c v where
  left := P.right
  right := P.left
  left_path := P.right_path
  right_path := P.left_path
  edges_disjoint := P.edges_disjoint.symm
  edges_cover e := by simpa only [or_comm] using P.edges_cover e
  support_cover x := by simpa only [or_comm] using P.support_cover x
  support_inter x hx hy := P.support_inter x hy hx

lemma left_support_subset (P : CyclePaths c v) : P.left.support ⊆ c.support :=
  fun _ h => (P.support_cover _).mp (Or.inl h)
lemma right_support_subset (P : CyclePaths c v) : P.right.support ⊆ c.support :=
  fun _ h => (P.support_cover _).mp (Or.inr h)
lemma left_edges_subset (P : CyclePaths c v) : P.left.edges ⊆ c.edges :=
  fun _ h => (P.edges_cover _).mp (Or.inl h)
lemma right_edges_subset (P : CyclePaths c v) : P.right.edges ⊆ c.edges :=
  fun _ h => (P.edges_cover _).mp (Or.inr h)

lemma exists_left_through (P : CyclePaths c v) {x : V} (hx : x ∈ c.support) :
    ∃ Q : CyclePaths c v, x ∈ Q.left.support := by
  rcases (P.support_cover x).mpr hx with hx | hx
  · exact ⟨P,hx⟩
  · exact ⟨P.swap,hx⟩
end CyclePaths

lemma switch_cyclePaths {u v : V} {c d : G.Walk u u} (huv : u ≠ v)
    (P : CyclePaths c v) (Q : CyclePaths d v) (hd : c.edges.Disjoint d.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v) :
    (P.left.append Q.left.reverse).IsCycle ∧
    (P.right.append Q.right.reverse).IsCycle ∧
    (P.left.append Q.left.reverse).edges.Disjoint (P.right.append Q.right.reverse).edges ∧
    (∀ e, (e ∈ (P.left.append Q.left.reverse).edges ∨
      e ∈ (P.right.append Q.right.reverse).edges) ↔ e ∈ c.edges ∨ e ∈ d.edges) := by
  have hpr : P.left.edges.Disjoint Q.left.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.left_edges_subset he1) (Q.left_edges_subset he2)
  have hps : P.left.edges.Disjoint Q.right.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.left_edges_subset he1) (Q.right_edges_subset he2)
  have hqr : P.right.edges.Disjoint Q.left.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.right_edges_subset he1) (Q.left_edges_subset he2)
  have hqs : P.right.edges.Disjoint Q.right.edges := by
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp hd (P.right_edges_subset he1) (Q.right_edges_subset he2)
  refine ⟨?_,?_,?_,?_⟩
  · apply append_isCycle_of_support_inter P.left_path Q.left_path.reverse huv
      (by simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using hpr)
    intro x hx hy
    exact hinter x (P.left_support_subset hx) (Q.left_support_subset (by simpa using hy))
  · apply append_isCycle_of_support_inter P.right_path Q.right_path.reverse huv
      (by simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using hqs)
    intro x hx hy
    exact hinter x (P.right_support_subset hx) (Q.right_support_subset (by simpa using hy))
  · simp only [Walk.edges_append,Walk.edges_reverse,List.disjoint_append_left,List.disjoint_append_right,
      List.disjoint_reverse_left,List.disjoint_reverse_right]
    exact ⟨⟨P.edges_disjoint,hqr.symm⟩,⟨hps,Q.edges_disjoint⟩⟩
  · intro e
    simp only [Walk.edges_append,List.mem_append,Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← Q.edges_cover e]
    tauto

lemma two_cycle_switch_through {u v x y : V} (c d : G.Walk u u)
    (hc : c.IsCycle) (hd : d.IsCycle) (huv : u ≠ v)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support)
    (hdis : c.edges.Disjoint d.edges)
    (hinter : ∀ z, z ∈ c.support → z ∈ d.support → z = u ∨ z = v)
    (hx : x ∈ c.support) (hy : y ∈ d.support) :
    ∃ r s : G.Walk u u, r.IsCycle ∧ s.IsCycle ∧ r.edges.Disjoint s.edges ∧
      (∀ e, (e ∈ r.edges ∨ e ∈ s.edges) ↔ e ∈ c.edges ∨ e ∈ d.edges) ∧
      x ∈ r.support ∧ y ∈ r.support := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hvc huv
  obtain ⟨Q⟩ := exists_cyclePaths d hd hvd huv
  obtain ⟨P,hxP⟩ := P.exists_left_through hx
  obtain ⟨Q,hyQ⟩ := Q.exists_left_through hy
  obtain ⟨hr,hs,hdis',hcover⟩ := switch_cyclePaths huv P Q hdis hinter
  refine ⟨P.left.append Q.left.reverse,P.right.append Q.right.reverse,hr,hs,hdis',hcover,?_,?_⟩
  · exact (Walk.mem_support_append_iff _ _).mpr (Or.inl hxP)
  · exact (Walk.mem_support_append_iff _ _).mpr (Or.inr (by simpa using hyQ))

lemma rigid_no_three_common_vertices [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v)) {u v : V}
    (p : G.Walk u u) (q : G.Walk v v) (hp : p.IsCycle) (hq : q.IsCycle)
    (hd : p.edges.Disjoint q.edges) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxp : x ∈ p.support) (hyp : y ∈ p.support) (hzp : z ∈ p.support)
    (hxq : x ∈ q.support) (hyq : y ∈ q.support) (hzq : z ∈ q.support) : False := by
  have hdis : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hd (p.mem_edges_toSubgraph.mp hep) (q.mem_edges_toSubgraph.mp heq)
  have hi := rigid_pair_intersection_le_two hrig heven p.toSubgraph q.toSubgraph
    (cycle_coe_regular G hp) (cycle_coe_regular G hq) hdis
  have hs : ({x,y,z} : Set V) ⊆ p.toSubgraph.verts ∩ q.toSubgraph.verts := by
    intro w hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨p.mem_verts_toSubgraph.mpr hxp,q.mem_verts_toSubgraph.mpr hxq⟩
    · exact ⟨p.mem_verts_toSubgraph.mpr hyp,q.mem_verts_toSubgraph.mpr hyq⟩
    · exact ⟨p.mem_verts_toSubgraph.mpr hzp,q.mem_verts_toSubgraph.mpr hzq⟩
  have hl := Set.ncard_le_ncard hs
  have ht : ({x,y,z} : Set V).ncard = 3 := by simp [hxy,hxz,hyz]
  omega

/-- If the third cycle meets the second and avoids both switching vertices,
it cannot meet either arc of the first cycle twice in a rigid graph. -/
lemma rigid_arc_contact_subsingleton [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v) (hvd : v ∈ d.support)
    (P : CyclePaths c v)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support) :
    ({x | x ∈ P.left.support ∧ x ∈ t.support} : Set V).Subsingleton := by
  obtain ⟨y,hyd,hyt⟩ := hmeet
  obtain ⟨Q⟩ := exists_cyclePaths d hd hvd huv
  obtain ⟨Q,hyQ⟩ := Q.exists_left_through hyd
  obtain ⟨hr,_,_,hcover⟩ := switch_cyclePaths huv P Q hcd hinter
  let r := P.left.append Q.left.reverse
  have hrt : r.edges.Disjoint t.edges := by
    apply List.disjoint_left.mpr
    intro e her het
    rcases (hcover e).mp (Or.inl her) with hec | hed
    · exact List.disjoint_left.mp hct hec het
    · exact List.disjoint_left.mp hdt hed het
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
  exact rigid_no_three_common_vertices hrig heven r t hr ht hrt hxz
    (hdist x (P.left_support_subset hx.1) hx.2) (hdist z (P.left_support_subset hz.1) hz.2)
    hxr hzr hyr hx.2 hz.2 hyt

lemma rigid_contacts_alternate [Fintype V] (hrig : CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v) (hvd : v ∈ d.support)
    (P : CyclePaths c v)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    {x z : V} (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    (x ∈ P.left.support ∧ z ∈ P.right.support) ∨
      (z ∈ P.left.support ∧ x ∈ P.right.support) := by
  have hl := rigid_arc_contact_subsingleton hrig heven hd ht huv hvd P hcd hct hdt hinter hut hvt hmeet
  have hr := rigid_arc_contact_subsingleton hrig heven hd ht huv hvd P.swap hcd hct hdt hinter hut hvt hmeet
  rcases (P.support_cover x).mpr hxc with hx | hx <;>
    rcases (P.support_cover z).mpr hzc with hz | hz
  · exact (hxz (hl ⟨hx,hxt⟩ ⟨hz,hzt⟩)).elim
  · exact Or.inl ⟨hx,hz⟩
  · exact Or.inr ⟨hz,hx⟩
  · exact (hxz (hr ⟨hx,hxt⟩ ⟨hz,hzt⟩)).elim

#print axioms rigid_no_three_common_vertices
#print axioms rigid_arc_contact_subsingleton
#print axioms rigid_contacts_alternate
#print axioms rigid_subfamily_number
#print axioms rigid_pair_intersection_le_two
#print axioms exists_cyclePaths
#print axioms two_cycle_switch_through
end Erdos184Work.RigidSwitching
