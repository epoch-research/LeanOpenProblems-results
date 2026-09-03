import Submission.LabelCycle

/-! Computable certificate records for finite labelled-kernel partitions.
Validity is checked by ordinary decidable propositions, not native axioms. -/
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {J W : Type*} [DecidableEq J] [DecidableEq W]

structure CycleData (J W : Type*) where
  size : ℕ
  edge : Fin (size+2) → J
  vertex : Fin (size+2) → W

namespace CycleData

def Valid (d : CycleData J W) (src dst : J → W) : Prop :=
  Function.Injective d.edge ∧ Function.Injective d.vertex ∧
  ∀ i, (src (d.edge i) = d.vertex i ∧ dst (d.edge i) = d.vertex (i+1)) ∨
    (dst (d.edge i) = d.vertex i ∧ src (d.edge i) = d.vertex (i+1))

instance validDecidable (d : CycleData J W) (src dst : J → W) : Decidable (d.Valid src dst) := by
  unfold Valid Function.Injective
  infer_instance

def support (d : CycleData J W) : Finset J := Finset.univ.image d.edge

def cycle (d : CycleData J W) (src dst : J → W) (h : d.Valid src dst) : Cycle src dst d.size where
  edge := d.edge
  vertex := d.vertex
  edge_injective := h.1
  vertex_injective := h.2.1
  endpoints := h.2.2

lemma circuit {d : CycleData J W} {src dst : J → W} (h : d.Valid src dst) :
    Circuit (code src dst) d.support := (d.cycle src dst h).circuit

lemma support_nonempty (d : CycleData J W) : d.support.Nonempty :=
  ⟨d.edge 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩

end CycleData

structure PartitionData (J W : Type*) where
  size : ℕ
  cycle : Fin size → CycleData J W

namespace PartitionData

def Valid (d : PartitionData J W) (src dst : J → W) (s : Finset J) : Prop :=
  (∀ i, (d.cycle i).Valid src dst) ∧
  (∀ i j, i ≠ j → Disjoint (d.cycle i).support (d.cycle j).support) ∧
  Finset.univ.biUnion (fun i => (d.cycle i).support) = s

instance validDecidable (d : PartitionData J W) (src dst : J → W) (s : Finset J) :
    Decidable (d.Valid src dst s) := by
  unfold Valid
  infer_instance

def pieces (d : PartitionData J W) : Finset (Finset J) :=
  Finset.univ.image (fun i => (d.cycle i).support)

lemma support_injective {d : PartitionData J W} {src dst : J → W} {s : Finset J}
    (h : d.Valid src dst s) : Function.Injective (fun i => (d.cycle i).support) := by
  intro i j hij
  by_contra hn
  obtain ⟨e,he⟩ := (d.cycle i).support_nonempty
  exact Finset.disjoint_left.mp (h.2.1 i j hn) he (by simpa only [← hij] using he)

lemma partition {d : PartitionData J W} {src dst : J → W} {s : Finset J}
    (h : d.Valid src dst s) : Partition (code src dst) s d.pieces := by
  refine ⟨?_,?_,?_⟩
  · intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact CycleData.circuit (h.1 i)
  · intro a ha b hb hab
    change a ∈ Finset.univ.image (fun i => (d.cycle i).support) at ha
    change b ∈ Finset.univ.image (fun i => (d.cycle i).support) at hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact h.2.1 i j (fun hij => hab (by subst j; rfl))
  · rw [← h.2.2]
    ext e
    simp [pieces]

lemma pieces_card {d : PartitionData J W} {src dst : J → W} {s : Finset J}
    (h : d.Valid src dst s) : d.pieces.card = d.size := by
  rw [pieces,Finset.card_image_of_injective _ (support_injective h),
    Finset.card_univ,Fintype.card_fin]

lemma exists_partition {d : PartitionData J W} {src dst : J → W} {s : Finset J}
    (h : d.Valid src dst s) : ∃ P, Partition (code src dst) s P ∧ P.card = d.size :=
  ⟨d.pieces,partition h,pieces_card h⟩

#print axioms exists_partition
end PartitionData
end Erdos184Work.LabelKernel
