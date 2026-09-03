import Submission.Work
import Submission.StarPathPieces
import Submission.BoundaryPorts
import Submission.InjectivePathReplacement

/-! Splice each exterior boundary arm into a different rooted core path. -/
namespace Erdos583PortSplicingDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583StarPathPiecesDevelopment Erdos583BoundaryPortsDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
variable {V I : Type*} {G : SimpleGraph V} {S : Set V}
  (start : I → V) (core : ∀ i, Arm G (start i))
  (slot : Boundary G S ↪ I) (hslot : ∀ b, start (slot b)=inner G S b)
  (outside : ∀ b : Boundary G S, Arm G (outer G S b))

noncomputable def splice (b : Boundary G S) :
    G.Walk (core (slot b)).finish (outside b).finish :=
  ((core (slot b)).walk.copy (hslot b) rfl).reverse.append
    (Walk.cons (adj G S b) (outside b).walk)

lemma splice_isPath (hc : ∀ i, ∀ x ∈ (core i).walk.support, x ∈ S)
    (ho : ∀ b, ∀ x ∈ (outside b).walk.support, x ∉ S) (b : Boundary G S) :
    (splice start core slot hslot outside b).IsPath := by
  apply Walk.IsPath.mk'
  simp only [splice,Walk.support_append,Walk.support_reverse,Walk.support_copy,
    Walk.support_cons,List.tail_cons,List.nodup_append]
  refine ⟨(by simpa only [Walk.support_reverse] using (core (slot b)).isPath.reverse.support_nodup),(outside b).isPath.support_nodup,?_⟩
  intro x hx y hy he
  subst y
  exact ho b x hy (hc (slot b) x (List.mem_reverse.mp hx))

lemma splice_edges (b : Boundary G S) :
    (splice start core slot hslot outside b).toSubgraph.edgeSet=
      (core (slot b)).walk.toSubgraph.edgeSet ∪
        ({edge G S b} ∪ (outside b).walk.toSubgraph.edgeSet) := by
  ext e
  simp only [splice,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_reverse,
    Walk.edges_copy,Walk.edges_cons,List.mem_append,List.mem_reverse,List.mem_cons,
    Set.mem_union,Set.mem_singleton_iff,Erdos583BoundaryPortsDevelopment.edge]

lemma path_edges_inside {a : V} (P : Arm G a) (hp : ∀ x ∈ P.walk.support, x ∈ S) :
    P.walk.toSubgraph.edgeSet ⊆ (within G S).edgeSet := by
  apply PentagonCarriers.subgraph_edges_within
  intro x hx
  exact hp x (P.walk.mem_verts_toSubgraph.mp hx)

section Decomposition
variable {A : Type*}
  (avoid : A → G.Subgraph)
  (hc : ∀ i, ∀ x ∈ (core i).walk.support, x ∈ S)
  (ho : ∀ b, ∀ x ∈ (outside b).walk.support, x ∉ S)
  (ha : ∀ a, (avoid a).edgeSet ⊆ (within G Sᶜ).edgeSet)
  (hcc : Pairwise (fun i j ↦ Disjoint (core i).walk.toSubgraph.edgeSet (core j).walk.toSubgraph.edgeSet))
  (hoo : Pairwise (fun b c ↦ Disjoint (outside b).walk.toSubgraph.edgeSet (outside c).walk.toSubgraph.edgeSet))
  (haa : Pairwise (fun a b ↦ Disjoint (avoid a).edgeSet (avoid b).edgeSet))
  (hao : ∀ a b, Disjoint (avoid a).edgeSet (outside b).walk.toSubgraph.edgeSet)

include hc ho in
lemma core_outside_disjoint (i : I) (b : Boundary G S) :
    Disjoint (core i).walk.toSubgraph.edgeSet (outside b).walk.toSubgraph.edgeSet :=
  (inside_disjoint_outside G S).mono (path_edges_inside (core i) (hc i))
    (path_edges_inside (outside b) (ho b))

include hc in
lemma core_boundary_disjoint (i : I) (b : Boundary G S) :
    Disjoint (core i).walk.toSubgraph.edgeSet ({edge G S b} : Set (Sym2 V)) := by
  apply Set.disjoint_singleton_right.mpr
  intro he
  exact edge_not_inside G S b (path_edges_inside (core i) (hc i) he)

include ho in
lemma boundary_outside_disjoint (b c : Boundary G S) :
    Disjoint ({edge G S b} : Set (Sym2 V)) (outside c).walk.toSubgraph.edgeSet := by
  apply Set.disjoint_singleton_left.mpr
  intro he
  exact edge_not_outside G S b (path_edges_inside (outside c) (ho c) he)

include hc ho hcc hoo in
lemma splice_disjoint : Pairwise (fun b c ↦
    Disjoint (splice start core slot hslot outside b).toSubgraph.edgeSet
      (splice start core slot hslot outside c).toSubgraph.edgeSet) := by
  intro b c hbc
  rw [splice_edges,splice_edges]
  simp only [Set.disjoint_union_left,Set.disjoint_union_right]
  refine ⟨⟨hcc (fun he ↦ hbc (slot.injective he)),
    (core_boundary_disjoint start core hc (slot c) b).symm,
    (core_outside_disjoint start core outside hc ho (slot c) b).symm⟩,?_,?_⟩
  · exact ⟨core_boundary_disjoint start core hc (slot b) c,
      Set.disjoint_singleton.mpr (fun he ↦ hbc (edge_injective G S he)),
      (boundary_outside_disjoint outside ho c b).symm⟩
  · exact ⟨core_outside_disjoint start core outside hc ho (slot b) c,
      boundary_outside_disjoint outside ho b c,hoo hbc⟩

include hc ho hcc in
lemma core_splice_disjoint (i : I) (b : Boundary G S) (hi : i ≠ slot b) :
    Disjoint (core i).walk.toSubgraph.edgeSet
      (splice start core slot hslot outside b).toSubgraph.edgeSet := by
  rw [splice_edges,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨hcc hi,core_boundary_disjoint start core hc i b,
    core_outside_disjoint start core outside hc ho i b⟩

include hc ha hao in
lemma avoid_splice_disjoint (a : A) (b : Boundary G S) :
    Disjoint (avoid a).edgeSet (splice start core slot hslot outside b).toSubgraph.edgeSet := by
  rw [splice_edges,Set.disjoint_union_right,Set.disjoint_union_right]
  refine ⟨(inside_disjoint_outside G S).symm.mono (ha a) (path_edges_inside (core (slot b)) (hc (slot b))),
    Set.disjoint_singleton_right.mpr (fun he ↦ edge_not_outside G S b (ha a he)),hao a b⟩

variable [Fintype I] [Fintype A]

include hc ho ha hcc hoo haa hao slot hslot in
lemma decomposition
    (hpath : ∀ a, IsPathSubgraph (avoid a))
    (hcore : (⋃ i, (core i).walk.toSubgraph.edgeSet)=(within G S).edgeSet)
    (hout : (⋃ a, (avoid a).edgeSet) ∪ (⋃ b, (outside b).walk.toSubgraph.edgeSet)=(within G Sᶜ).edgeSet) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ Fintype.card I+Fintype.card A := by
  let f : I ⊕ A → G.Subgraph := Sum.elim (fun i ↦ (core i).walk.toSubgraph) avoid
  let g (b : Boundary G S) := (splice start core slot hslot outside b).toSubgraph
  let slots : Boundary G S → I ⊕ A := fun b ↦ Sum.inl (slot b)
  have hslots : Function.Injective slots := fun b c he ↦ slot.injective (Sum.inl.inj he)
  have hff : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet) := by
    rintro (i|a) (j|b) hne
    · exact hcc (fun he ↦ hne (congrArg Sum.inl he))
    · exact (inside_disjoint_outside G S).mono (path_edges_inside (core i) (hc i)) (ha b)
    · exact (inside_disjoint_outside G S).symm.mono (ha a) (path_edges_inside (core j) (hc j))
    · exact haa (fun he ↦ hne (congrArg Sum.inr he))
  have hfg : ∀ i b, i ≠ slots b → Disjoint (f i).edgeSet (g b).edgeSet := by
    rintro (i|a) b hi
    · exact core_splice_disjoint start core slot hslot outside hc ho hcc i b
        (fun he ↦ hi (congrArg Sum.inl he))
    · exact avoid_splice_disjoint start core slot hslot outside avoid hc ha hao a b
  have hsub : ∀ b, (f (slots b)).edgeSet ⊆ (g b).edgeSet := by
    intro b
    dsimp only [f,g,slots,Sum.elim_inl]
    rw [splice_edges]
    exact Set.subset_union_left
  have hcover : (⋃ i, (f i).edgeSet) ∪ (⋃ b, (g b).edgeSet)=G.edgeSet := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (Set.iUnion_subset fun i ↦ (f i).edgeSet_subset)
        (Set.iUnion_subset fun b ↦ (g b).edgeSet_subset)
    · intro e he
      rw [←cover G S] at he
      rcases he with hcE|⟨b,rfl⟩|hoE
      · rw [←hcore] at hcE
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hcE
        exact Or.inl (Set.mem_iUnion.mpr ⟨Sum.inl i,hi⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨b,by dsimp only [g]; rw [splice_edges]; exact Or.inr (Or.inl rfl)⟩)
      · rw [←hout] at hoE
        rcases hoE with hoE|hoE
        · obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hoE
          exact Or.inl (Set.mem_iUnion.mpr ⟨Sum.inr a,ha⟩)
        · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hoE
          exact Or.inr (Set.mem_iUnion.mpr ⟨b,by dsimp only [g]; rw [splice_edges]; exact Or.inr (Or.inr hb)⟩)
  obtain ⟨D,hD,hn⟩ := Erdos583InjectivePathReplacementDevelopment.replace_injective f g slots hslots
    (by rintro (i|a); exact ⟨_,_,(core i).walk,(core i).isPath,rfl⟩; exact hpath a)
    (fun b ↦ ⟨_,_,_,splice_isPath start core slot hslot outside hc ho b,rfl⟩)
    hff (splice_disjoint start core slot hslot outside hc ho hcc hoo) hfg hsub hcover
  exact ⟨D,hD,by simpa only [Fintype.card_sum] using hn⟩

end Decomposition
end Erdos583PortSplicingDevelopment
