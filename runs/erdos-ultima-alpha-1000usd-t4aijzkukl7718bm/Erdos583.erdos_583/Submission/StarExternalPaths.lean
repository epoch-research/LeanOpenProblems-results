import Submission.StarContraction
import Submission.StarPathPieces
import Submission.ArmExtension
import Submission.BoundaryPorts

/-! Lift the path pieces outside a contracted center and assign them to original boundary edges. -/
namespace Erdos583StarExternalPathsDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.BridgeGlue
open Erdos583StarContractionDevelopment Erdos583StarPathPiecesDevelopment
open Erdos583ArmExtensionDevelopment Erdos583BoundaryPortsDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V} {S : Set V} {r : V} (hr : r ∈ S)
  {k : ℕ} (T : TrailFamily (contract G S r hr) k) (hp : ∀ i, (T.walk i).IsPath)

lemma outside_graph : within (contract G S r hr) ({r}ᶜ : Set V)=within G Sᶜ := by
  ext x y
  constructor
  · rintro ⟨hxy,hx,hy⟩
    exact exterior_edge G S r hr hxy hx hy
  · rintro ⟨hxy,hx,hy⟩
    exact ⟨Or.inl ⟨hxy,hx,hy⟩,fun he ↦ hx (he.symm ▸ hr),fun he ↦ hy (he.symm ▸ hr)⟩

noncomputable def armPath (e : ArmIndex T hp r) : Arm G (tip T hp r e) :=
  { finish := (familyHalf T hp r e.val).finish
    walk := lift G S r hr (familyHalf T hp r e.val).walk.tail (tail_avoids_center T hp r e)
    isPath := lift_isPath G S r hr _ _ (familyHalf T hp r e.val).isPath.tail }

lemma armPath_edges (e : ArmIndex T hp r) :
    (armPath hr T hp e).walk.toSubgraph.edgeSet=(familyHalf T hp r e.val).walk.tail.toSubgraph.edgeSet :=
  lift_edges G S r hr _ (tail_avoids_center T hp r e)

lemma armPath_outside (e : ArmIndex T hp r) : ∀ x ∈ (armPath hr T hp e).walk.support, x ∉ S := by
  rw [show (armPath hr T hp e).walk.support=(familyHalf T hp r e.val).walk.tail.support from lift_support G S r hr _ (tail_avoids_center T hp r e)]
  apply support_outside G S r hr _ (tail_avoids_center T hp r e)
  exact ((adj_center G S r hr).mp (tip_adj T hp r e)).1

lemma armPath_disjoint : Pairwise (fun e f : ArmIndex T hp r ↦
    Disjoint (armPath hr T hp e).walk.toSubgraph.edgeSet (armPath hr T hp f).walk.toSubgraph.edgeSet) := by
  intro e f hne
  rw [armPath_edges,armPath_edges]
  exact tail_disjoint T hp r hne

noncomputable def boundaryOfArm (e : ArmIndex T hp r) : Boundary G S := by
  have hh := (adj_center G S r hr).mp (tip_adj T hp r e)
  let x := Classical.choose hh.2
  have hx := Classical.choose_spec hh.2
  exact ⟨(⟨x,hx.1⟩,⟨tip T hp r e,hh.1⟩),hx.2⟩

lemma boundaryOfArm_outer (e : ArmIndex T hp r) : outer G S (boundaryOfArm hr T hp e)=tip T hp r e := rfl

lemma boundaryOfArm_injective : Function.Injective (boundaryOfArm hr T hp) := by
  intro e f he
  exact tip_injective T hp r (congrArg (outer G S) he)

noncomputable def armEmbedding : ArmIndex T hp r ↪ Boundary G S :=
  ⟨boundaryOfArm hr T hp,boundaryOfArm_injective hr T hp⟩

noncomputable def exterior (b : Boundary G S) : Arm G (outer G S b) :=
  extend (tip T hp r) (outer G S) (armEmbedding hr T hp) (fun _ ↦ rfl) (armPath hr T hp) b

lemma exterior_outside : ∀ b, ∀ x ∈ (exterior hr T hp b).walk.support, x ∉ S :=
  extend_support _ _ _ _ _ Sᶜ (outer_not_mem G S) (armPath_outside hr T hp)

lemma exterior_disjoint : Pairwise (fun b c ↦ Disjoint (exterior hr T hp b).walk.toSubgraph.edgeSet
    (exterior hr T hp c).walk.toSubgraph.edgeSet) :=
  extend_disjoint _ _ _ _ _ (armPath_disjoint hr T hp)

noncomputable def avoiding (a : AvoidIndex T r) : G.Subgraph :=
  (lift G S r hr (T.walk a.val) a.property).toSubgraph

lemma avoiding_edges (a : AvoidIndex T r) : (avoiding hr T a).edgeSet=(T.walk a.val).toSubgraph.edgeSet :=
  lift_edges G S r hr _ _

include hp in
lemma avoiding_isPath (a : AvoidIndex T r) : IsPathSubgraph (avoiding hr T a) :=
  ⟨_,_,_,lift_isPath G S r hr _ a.property (hp a.val),rfl⟩

lemma avoiding_subset (a : AvoidIndex T r) : (avoiding hr T a).edgeSet ⊆ (within G Sᶜ).edgeSet := by
  rw [avoiding_edges,←outside_graph hr]
  apply PentagonCarriers.subgraph_edges_within
  intro x hx
  exact fun he ↦ a.property (he ▸ (T.walk a.val).mem_verts_toSubgraph.mp hx)

lemma avoiding_disjoint : Pairwise (fun a b : AvoidIndex T r ↦ Disjoint (avoiding hr T a).edgeSet
    (avoiding hr T b).edgeSet) := by
  intro a b hab
  rw [avoiding_edges,avoiding_edges]
  exact T.disjoint (fun he ↦ hab (Subtype.ext he))

lemma avoiding_arm_disjoint (a : AvoidIndex T r) (e : ArmIndex T hp r) :
    Disjoint (avoiding hr T a).edgeSet (armPath hr T hp e).walk.toSubgraph.edgeSet := by
  rw [avoiding_edges,armPath_edges]
  have hne : a.val ≠ e.val.1 := by
    intro he
    exact a.property (he ▸ arm_owner_touches T hp r e)
  exact (T.disjoint hne).mono_right
    ((tail_edges_subset _ e.property).trans (half_edges_subset _ (hp e.val.1) r e.val.2))

lemma avoiding_exterior_disjoint (a : AvoidIndex T r) (b : Boundary G S) :
    Disjoint (avoiding hr T a).edgeSet (exterior hr T hp b).walk.toSubgraph.edgeSet :=
  extend_disjoint_left _ _ _ _ _ _ (avoiding_arm_disjoint hr T hp a) b

lemma exterior_cover : (⋃ a, (avoiding hr T a).edgeSet) ∪
    (⋃ b, (exterior hr T hp b).walk.toSubgraph.edgeSet)=(within G Sᶜ).edgeSet := by
  simp only [exterior,extend_union,armPath_edges,avoiding_edges]
  rw [←outside_cover T hp r,outside_graph hr]

end Erdos583StarExternalPathsDevelopment
