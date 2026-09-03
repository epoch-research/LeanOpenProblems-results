import Submission.NumberedCycleSegmentation
import Submission.PathKernelTransport

/-! Arbitrary finite contact layouts produce labelled kernels, with exact
edge coverage for every original cycle and every subfamily. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
open PathSubstitution
set_option maxHeartbeats 2000000
variable {V W K : Type*} [Fintype V] {G : SimpleGraph V}

lemma ContactLayout.exists_ordered_family (m : K → ℕ)
    (place : ∀ k, Fin (m k+2) → W) (hplace : ∀ k, Function.Injective (place k))
    (vertex : W → V) (root : K → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout (fun k => m k+2) place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) :
    ∃ o : ∀ k, Marked.Order (m k), ∃ F : Family (Σ k, Fin (m k+2)) W G,
      F.vertex = vertex ∧
      F.src = (fun j => place j.1 j.2) ∧
      F.dst = (fun j => place j.1 (Marked.nextFin (m j.1) (o j.1) j.2)) ∧
      (∀ k e, e ∈ (C k).edges ↔ ∃ i, e ∈ (F.path ⟨k,i⟩).edges) ∧
      (∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) := by
  have hseg (k : K) := Marked.exists_numbered_segmentation (C k) (hC k) (m k)
    (vertex ∘ place k) (L.injective.comp (hplace k))
    (fun i => L.mem ⟨i,rfl⟩)
  choose o hS using hseg
  let S k := Classical.choice (hS k)
  have hn (k : K) (i : Fin (m k+2)) : place k i ≠ place k (Marked.nextFin (m k) (o k) i) :=
    fun h => Marked.nextFin_ne (m k) (o k) i (hplace k h)
  let F := assemble_segments (fun k => m k+2) vertex L.injective place
    (fun _ => id) (fun k => Marked.nextFin (m k) (o k)) hn (fun _ => Function.surjective_id)
    root C hC S hdisC (fun w k => (L.points k w).mp) L.meet
  refine ⟨o,F,rfl,rfl,rfl,?_,?_⟩
  · intro k e
    exact (S k).cover e
  · exact assemble_segments_cover (fun k => m k+2) vertex L.injective place
      (fun _ => id) (fun k => Marked.nextFin (m k) (o k)) hn (fun _ => Function.surjective_id)
      root C hC S hdisC (fun w k => (L.points k w).mp) L.meet hcover

end Erdos184Work.CycleSegments

namespace Erdos184Work.PathSubstitution.Family
set_option maxHeartbeats 1500000
variable {V W K : Type*} [Fintype V] [Fintype K] {G : SimpleGraph V}
    {m : K → ℕ} (F : Family (Σ k, Fin (m k)) W G)

noncomputable def colorLabels (A : Finset K) : Finset (Σ k, Fin (m k)) :=
  Finset.univ.filter (fun j => j.1 ∈ A)

lemma expandGraph_colorLabels
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k))
    (hpiece : ∀ k e, e ∈ (C k).edges ↔ ∃ i, e ∈ (F.path ⟨k,i⟩).edges)
    (A : Finset K) :
    F.expandGraph (colorLabels A) = subfamilyGraph (A.image (fun k => (C k).toSubgraph)) := by
  apply SimpleGraph.edgeSet_injective
  ext e
  rw [F.mem_expandGraph,subfamilyGraph_edges]
  simp only [colorLabels,Finset.mem_filter,Finset.mem_univ,true_and,
    Set.mem_iUnion,exists_prop,Finset.mem_image]
  constructor
  · rintro ⟨⟨k,i⟩,hk,he⟩
    exact ⟨(C k).toSubgraph,⟨k,hk,rfl⟩,(C k).mem_edges_toSubgraph.mpr ((hpiece k e).mpr ⟨i,he⟩)⟩
  · rintro ⟨H,⟨k,hk,rfl⟩,he⟩
    obtain ⟨i,hi⟩ := (hpiece k e).mp ((C k).mem_edges_toSubgraph.mp he)
    exact ⟨⟨k,i⟩,hk,hi⟩

#print axioms expandGraph_colorLabels
end Erdos184Work.PathSubstitution.Family
#print axioms Erdos184Work.CycleSegments.ContactLayout.exists_ordered_family
