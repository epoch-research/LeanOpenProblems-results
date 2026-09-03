import Submission.CanonicalRotation

/-! The obstruction forced by two-ended singleton-token exchanges. -/
open SimpleGraph Erdos583Work Erdos583Work.PendantCompletion
open Erdos583CanonicalRotationDevelopment
namespace Erdos583TokenObstructionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma cycle_of_no_dead_end {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : ∃ a b, G.Adj a b)
    (hnext : ∀ {a b}, G.Adj a b → ∃ c, G.Adj b c ∧ c ≠ a) : ¬G.IsAcyclic := by
  classical
  intro hacyc
  obtain ⟨a,b,hab⟩ := he
  let C := G.connectedComponentMk a
  let a' : C := ⟨a,rfl⟩
  let b' : C := ⟨b,(C.mem_supp_congr_adj hab).mp rfl⟩
  letI : Nontrivial C := ⟨⟨a',b',fun hh ↦ hab.ne (congrArg Subtype.val hh)⟩⟩
  obtain ⟨x,hx⟩ := (hacyc.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  obtain ⟨y,hxy,hy⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
  obtain ⟨z,hxz,hzy⟩ := hnext (G.symm hxy)
  let z' : C := ⟨z,C.mem_supp_of_adj_mem_supp x.property hxz⟩
  exact hzy (congrArg Subtype.val (hy z' hxz))

structure MaxNormal {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph) : Prop where
  good : GoodDecomposition G D
  nonempty : ∀ H ∈ D, H.edgeSet.Nonempty
  bound : ∀ v, endpointMultiplicity D v ≤ 2
  maximal : ∀ E : Finset G.Subgraph, GoodDecomposition G E →
    (∀ H ∈ E, H.edgeSet.Nonempty) → (∀ v, endpointMultiplicity E v ≤ 2) →
    (inactive E).card ≤ (inactive D).card

lemma single_edge_not_inactive {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} {a b : V} (h : G.Adj a b) (hmem : G.subgraphOfAdj h ∈ D) :
    a ∉ inactive D ∧ b ∉ inactive D := by
  classical
  have hp : (Walk.cons h Walk.nil).IsPath := by simp [h.ne]
  have hpos (x : V) (hx : x=a ∨ x=b) : x ∉ inactive D := by
    have hdeg : ((G.subgraphOfAdj h).neighborSet x).ncard = 1 := by
      simpa using (Erdos583Work.EndpointSelection.path_neighbor_one_iff hp (by simp) x).mpr hx
    have hpos : 0 < endpointMultiplicity D x :=
      Finset.card_pos.mpr ⟨_,Finset.mem_filter.mpr ⟨hmem,hdeg⟩⟩
    intro hx
    have hz : endpointMultiplicity D x = 0 := (Finset.mem_filter.mp hx).2
    omega
  exact ⟨hpos a (Or.inl rfl),hpos b (Or.inr rfl)⟩

def TokenWitness {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : Finset V) (a b : V) : Prop :=
  ∃ D : Finset G.Subgraph, MaxNormal G D ∧ ∃ h : G.Adj a b,
    G.subgraphOfAdj h ∈ D ∧ insert a (insert b (inactive D)) = C

lemma tokenWitness_symm {V : Type*} [Fintype V] {G : SimpleGraph V}
    {C : Finset V} {a b : V} (h : TokenWitness G C a b) : TokenWitness G C b a := by
  classical
  obtain ⟨D,hD,hab,hmem,hC⟩ := h
  refine ⟨D,hD,hab.symm,?_,?_⟩
  · rw [G.subgraphOfAdj_symm hab]; exact hmem
  · rw [Finset.insert_comm]
    exact hC

def tokenGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V) : SimpleGraph C where
  Adj a b := TokenWitness G C a.val b.val
  symm _ _ h := tokenWitness_symm h
  loopless _ h := h.choose_spec.2.choose.ne rfl

lemma tokenGraph_le {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V) :
    tokenGraph G C ≤ G.induce (C : Set V) := by
  intro a b h
  exact h.choose_spec.2.choose

lemma tokenWitness_step {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (heven : ∀ v, Even (G.degree v))
    {C : Finset V} {a b : V} (h : TokenWitness G C a b) :
    ∃ z ∈ C, TokenWitness G C b z ∧ z ≠ a := by
  classical
  obtain ⟨D,hD,hab,hmem,hC⟩ := h
  obtain ⟨E,hE,hEn,hEb,hEmax,z,hz,hbz,hI,hmem'⟩ := normal_single_edge_exchange
    hD.good hD.nonempty hD.bound heven hD.maximal hab.symm
      (by rw [G.subgraphOfAdj_symm hab]; exact hmem)
  have hza : z ≠ a := fun hh ↦ (single_edge_not_inactive hab hmem).1 (hh ▸ hz)
  have hzC : z ∈ C := by rw [←hC]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
  refine ⟨z,hzC,⟨E,⟨hE,hEn,hEb,hEmax⟩,hbz,hmem',?_⟩,hza⟩
  rw [←hC,hI]
  ext w
  by_cases hw : w=z
  · subst w
    simp [hz]
  · simp [hw,or_left_comm]

/-- If a globally maximal normal Eulerian partition contains a singleton edge
ab, then the inactive vertices together with a and b must induce a cycle. -/
lemma singleton_token_cycle_obstruction {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : MaxNormal G D)
    (heven : ∀ v, Even (G.degree v)) {a b : V} (hab : G.Adj a b)
    (hmem : G.subgraphOfAdj hab ∈ D) :
    ¬(G.induce ((insert a (insert b (inactive D)) : Finset V) : Set V)).IsAcyclic := by
  classical
  let C := insert a (insert b (inactive D))
  have hab' : (tokenGraph G C).Adj (⟨a,by simp [C]⟩ : C) (⟨b,by simp [C]⟩ : C) :=
    ⟨D,hD,hab,hmem,rfl⟩
  have hcycle := cycle_of_no_dead_end (tokenGraph G C) ⟨_,_,hab'⟩ (fun {x y} hxy ↦ ?_)
  · intro hA
    exact hcycle (hA.anti (tokenGraph_le G C))
  · obtain ⟨z,hz,hzy,hzx⟩ := tokenWitness_step heven hxy
    exact ⟨⟨z,hz⟩,hzy,fun hh ↦ hzx (congrArg Subtype.val hh)⟩

end Erdos583TokenObstructionDevelopment
