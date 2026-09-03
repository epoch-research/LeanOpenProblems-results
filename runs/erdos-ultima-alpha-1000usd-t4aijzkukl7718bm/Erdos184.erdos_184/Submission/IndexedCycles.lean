import Submission.ContactLayouts

/-! Indexed cycle unions and restriction to their edges. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.IndexedCycles
open MaximumCycles RigidSwitching
set_option maxHeartbeats 1500000
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

noncomputable def image (root : I → V) (C : ∀ i, G.Walk (root i) (root i)) : Finset G.Subgraph :=
  Finset.univ.image (fun i => (C i).toSubgraph)

variable (root : I → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle) (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)

include hC in
lemma regular : ∀ H ∈ image root C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  rintro H hH
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  exact cycle_coe_regular G (hC i)

include hd in
lemma disjoint : Set.PairwiseDisjoint (image root C : Set G.Subgraph) (fun H => H.edgeSet) := by
  intro H hH K hK hne
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
  apply Set.disjoint_left.mpr
  intro e he hf
  exact List.disjoint_left.mp (hd i j (fun he => hne (by subst j; rfl)))
    ((C i).mem_edges_toSubgraph.mp he) ((C j).mem_edges_toSubgraph.mp hf)

include hC hd in
lemma injective : Function.Injective (fun i => (C i).toSubgraph) := by
  intro i j he
  dsimp only at he
  have heE := congrArg (fun H : G.Subgraph => H.edgeSet) he
  dsimp only at heE
  by_contra hne
  have hnon := (hC i).not_nil
  have hmem : s(root i,(C i).snd) ∈ (C i).toSubgraph.edgeSet := (C i).toSubgraph_adj_snd hnon
  exact List.disjoint_left.mp (hd i j hne) ((C i).mem_edges_toSubgraph.mp hmem)
    ((C j).mem_edges_toSubgraph.mp (by rw [← heE]; exact hmem))

include hC hd in
lemma card : (image root C).card = Fintype.card I := by
  rw [image,Finset.card_image_of_injective _ (injective root C hC hd),Finset.card_univ]

include hC hd in
lemma number (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    Critical.number (subfamilyGraph (image root C)) = Fintype.card I := by
  rw [rigid_subfamily_number hrig heven (image root C) (regular root C hC) (disjoint root C hd),
    card root C hC hd]

include hC hd in
lemma even : ∀ v, Even ((subfamilyGraph (image root C)).degree v) :=
  cycle_subfamily_even (image root C) (regular root C hC) (disjoint root C hd)

include hC hd in
lemma rigid (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    Rigidity.CycleRigid (subfamilyGraph (image root C)) :=
  rigid_subfamily hrig heven (image root C) (regular root C hC) (disjoint root C hd)

lemma edges (e : Sym2 V) : e ∈ (subfamilyGraph (image root C)).edgeSet ↔ ∃ i, e ∈ (C i).edges := by
  rw [subfamilyGraph_edges]
  simp only [Set.mem_iUnion,exists_prop,image,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨H,⟨i,rfl⟩,he⟩
    exact ⟨i,(C i).mem_edges_toSubgraph.mp he⟩
  · rintro ⟨i,he⟩
    exact ⟨(C i).toSubgraph,⟨i,rfl⟩,(C i).mem_edges_toSubgraph.mpr he⟩

lemma edges_subset (i : I) : ∀ e ∈ (C i).edges, e ∈ (subfamilyGraph (image root C)).edgeSet :=
  fun e he => (edges root C e).mpr ⟨i,he⟩

noncomputable def restrict (i : I) : (subfamilyGraph (image root C)).Walk (root i) (root i) :=
  (C i).transfer _ (edges_subset root C i)

lemma restrict_edges (i : I) : (restrict root C i).edges = (C i).edges := Walk.edges_transfer _ _
lemma restrict_support (i : I) : (restrict root C i).support = (C i).support := Walk.support_transfer _ _
include hC in
lemma restrict_cycle (i : I) : (restrict root C i).IsCycle := (hC i).transfer _
include hd in
lemma restrict_disjoint : ∀ i j, i ≠ j → (restrict root C i).edges.Disjoint (restrict root C j).edges := by
  simpa only [restrict_edges] using hd
lemma restrict_cover : ∀ x y, (subfamilyGraph (image root C)).Adj x y →
    ∃ i, s(x,y) ∈ (restrict root C i).edges := by
  intro x y hxy
  simpa only [restrict_edges] using (edges root C s(x,y)).mp hxy

include hC hd in
lemma number_of_cover (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (hcover : ∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges) :
    Critical.number G = Fintype.card I := by
  have heq : subfamilyGraph (image root C) = G := by
    apply le_antisymm (subfamilyGraph_le _)
    intro x y hxy
    exact (edges root C s(x,y)).mpr (hcover x y hxy)
  rw [← heq]
  exact number root C hC hd hrig heven

#print axioms number_of_cover
#print axioms restrict_cycle
end Erdos184Work.IndexedCycles
