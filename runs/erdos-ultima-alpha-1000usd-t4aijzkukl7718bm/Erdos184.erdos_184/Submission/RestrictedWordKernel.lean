import Submission.WordKernelSuppression

/-! Restriction to a color subfamily, followed by suppression of any marker
private within that subfamily. No arbitrary graph or path family is required. -/
open scoped Classical
namespace Erdos184Work.WordKernel
open Erdos184Serial LabelKernel
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {K W : Type*} [DecidableEq K] [DecidableEq W] {n : K → ℕ}

noncomputable local instance {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable (place : ∀ i, Fin (n i+2) → W) (A : Finset K)

def restrictedPlace (i : A) : Fin (n i.val+2) → W := place i.val

def restrictEdge : (Σ i : A, Fin (n i.val+2)) ↪ (Σ i : K, Fin (n i+2)) :=
  Function.Embedding.sigmaMap (Function.Embedding.subtype _) (fun _ => Function.Embedding.refl _)

def restrictEmbedding : Embedding
    (source (restrictedPlace place A)) (target (restrictedPlace place A))
    (source place) (target place) where
  edge := restrictEdge A
  vertex := Function.Embedding.refl W
  endpoints _ := rfl

lemma restrict_univ [Fintype K] :
    (Finset.univ : Finset (Σ i : A, Fin (n i.val+2))).map (restrictEdge A) =
      Finset.univ.filter (fun e : Σ i : K, Fin (n i+2) => e.1 ∈ A) := by
  ext e
  simp only [Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ⟨j,rfl⟩
    exact j.1.property
  · intro he
    exact ⟨⟨⟨e.1,he⟩,e.2⟩,rfl⟩

noncomputable def restrictTransport :
    SupportTransport (code (source (restrictedPlace place A)) (target (restrictedPlace place A)))
      (code (source place) (target place)) :=
  SupportTransport.ofEmbedding (restrictEmbedding place A).edge (restrictEmbedding place A).valid_map

lemma restriction_spectrum [Fintype K] (P : ℕ → Prop) :
    (∃ D, Partition (code (source place) (target place))
      (Finset.univ.filter (fun e : Σ i : K, Fin (n i+2) => e.1 ∈ A)) D ∧ P D.card) ↔
    (∃ D, Partition (code (source (restrictedPlace place A)) (target (restrictedPlace place A)))
      Finset.univ D ∧ P D.card) := by
  have h := (restrictTransport place A).exists_partition_card_iff Finset.univ P
  change (∃ D, Partition _ (Finset.univ.map (restrictEdge A)) D ∧ _) ↔ _ at h
  rwa [restrict_univ] at h

variable (hinj : ∀ i, Function.Injective (place i))
    (i : A) (j : Fin (n i.val+2))
    (hprivate : ∀ k ∈ A, ∀ r : Fin (n k+2), place k r = place i.val j → k = i.val)

noncomputable def restrictedSuppression (hsize : 1 ≤ n i.val) :
    Suppression (source (restrictedPlace place A)) (target (restrictedPlace place A)) :=
  suppression (restrictedPlace place A) (fun k => hinj k.val) i j
    (fun k r h => Subtype.ext (hprivate k.val k.property r h)) hsize

noncomputable def restrictSuppressTransport (hsize : 1 ≤ n i.val) :
    SupportTransport
      (code (restrictedSuppression place A hinj i j hprivate hsize).source
        (restrictedSuppression place A hinj i j hprivate hsize).target)
      (code (source place) (target place)) :=
  (restrictedSuppression place A hinj i j hprivate hsize).transport.trans (restrictTransport place A)

lemma restrictSuppress_full [Fintype K] (hsize : 1 ≤ n i.val) :
    (restrictSuppressTransport place A hinj i j hprivate hsize).expand Finset.univ =
      Finset.univ.filter (fun e : Σ k : K, Fin (n k+2) => e.1 ∈ A) := by
  change ((restrictedSuppression place A hinj i j hprivate hsize).transport.expand
    Finset.univ).map (restrictEdge A) = _
  rw [Suppression.expand_univ,restrict_univ]

lemma restrictSuppress_spectrum [Fintype K] (hsize : 1 ≤ n i.val) (P : ℕ → Prop) :
    (∃ D, Partition (code (source place) (target place))
      (Finset.univ.filter (fun e : Σ k : K, Fin (n k+2) => e.1 ∈ A)) D ∧ P D.card) ↔
    (∃ D, Partition
      (code (restrictedSuppression place A hinj i j hprivate hsize).source
        (restrictedSuppression place A hinj i j hprivate hsize).target)
      Finset.univ D ∧ P D.card) := by
  have h := (restrictSuppressTransport place A hinj i j hprivate hsize).exists_partition_card_iff
    Finset.univ P
  rwa [restrictSuppress_full] at h

#print axioms restriction_spectrum
#print axioms restrictSuppress_spectrum
end Erdos184Work.WordKernel
