import Submission.FastCanonicalPlace
import Submission.SmallKernelRejection
import Submission.CanonicalThreeReduction

/-! Flattening the canonical sigma edge labels into a single finite interval.
This exposes a kernel-reducible endpoint table for finite rejection certificates. -/
namespace Erdos184Work.FlatCanonicalKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
    (o : ∀ i, Marked.Order (arity b i))

noncomputable local instance {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

def size : ℕ := ∑ i, (arity b i + 2)

def edge : Fin (size b) ≃ (Σ i, Fin (arity b i+2)) := (finSigmaFinEquiv (n := fun i => arity b i+2)).symm

def src (e : Fin (size b)) : Fin ((l*l)*2) := fastSource b hb o (edge b e)
def dst (e : Fin (size b)) : Fin ((l*l)*2) := fastTarget b hb o (edge b e)
def color (e : Fin (size b)) : Fin l := (edge b e).1

noncomputable def embedding : Embedding (src b hb o) (dst b hb o)
    (source b hb o) (target b hb o) where
  edge := (edge b).toEmbedding
  vertex := Function.Embedding.refl _
  endpoints e := by
    change s(fastSource b hb o (edge b e),fastTarget b hb o (edge b e)) = _
    rw [source_eq_fast,target_eq_fast]
    rfl

lemma map_univ : (Finset.univ : Finset (Fin (size b))).map (embedding b hb o).edge = Finset.univ :=
  Finset.map_univ_equiv (edge b)

lemma map_selected (A : Finset (Fin l)) :
    (selected (color b) A).map (embedding b hb o).edge = PathSubstitution.Family.colorLabels A := by
  ext e
  simp only [selected,PathSubstitution.Family.colorLabels,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_map]
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact hf
  · intro he
    refine ⟨(edge b).symm e,?_,(edge b).apply_symm_apply e⟩
    change (edge b ((edge b).symm e)).1 ∈ A
    rwa [(edge b).apply_symm_apply]

lemma rejects {d : RejectionData (Fin (size b)) (Fin ((l*l)*2)) (Fin l)}
    (hd : d.Valid (src b hb o) (dst b hb o) (color b)) :
    ¬ CanonicalThreeReduction.Restrictions b hb o := by
  intro h
  apply RejectionData.sound hd
  · have hh := (embedding b hb o).hasNumber_map_iff Finset.univ 3
    rw [map_univ] at hh
    exact hh.mp h.1.1
  · intro A P hP
    obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists (embedding b hb o).edge (embedding b hb o).valid_map hP
    rw [map_selected] at hQ
    have hh := h.2.2.1 A Q hQ
    omega
  · intro A hA
    obtain ⟨Q,hQ,hcQ⟩ := h.2.2.2 A hA
    rw [← map_selected b hb o A] at hQ
    obtain ⟨P,hP,hcP⟩ := unmap_partition_exists (embedding b hb o).edge (embedding b hb o).valid_map hQ
    exact ⟨P,hP,hcP.trans_le hcQ⟩

#print axioms rejects
end Erdos184Work.FlatCanonicalKernel
