import Submission.CyclicWordCoarsening
import Submission.CanonicalWordFormat
import Submission.FastCanonicalPlace

/-! Restricting a canonical pair kernel to selected colors and deleting all
markers private in that restriction. The retained cyclic words and endpoint
functions are computable. -/
open scoped Classical
namespace Erdos184Work.CanonicalSubsetCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (arity b i))

noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

def fastWord (i : Fin l) (j : Fin (arity b i+2)) : Fin ((l*l)*2) :=
  fastPlace b hb i ((SmallOrderNormalization.normalized (arity b i) (o i)).vertex j)

lemma word_eq_fast : CanonicalPairKernel.word b hb o = fastWord b hb o := by
  funext i j
  unfold CanonicalPairKernel.word NormalizedKernel.word fastWord
  rw [place_eq_fast]

lemma fastWord_injective (i : Fin l) : Function.Injective (fastWord b hb o i) := by
  rw [← word_eq_fast]
  exact word_injective b hb o i

lemma fastWord_mem (i : Fin l) (j : Fin (arity b i+2)) : fastWord b hb o i j ∈ markers b i :=
  fastPlace_mem b hb i _

lemma fastWord_range (i : Fin l) (z : Fin ((l*l)*2)) :
    (∃ j, fastWord b hb o i j = z) ↔ z ∈ markers b i := by
  rw [← word_eq_fast]
  exact word_range b hb o i z

variable (A : Finset (Fin l))

def retained (i : Fin l) : Finset (Fin ((l*l)*2)) :=
  markers b i ∩ (A.erase i).biUnion (markers b)

def keep (i : A) : Finset (Fin (arity b i.val+2)) :=
  Finset.univ.filter (fun j => fastWord b hb o i.val j ∈ retained b A i.val)

lemma keep_image (i : A) : (keep b hb o A i).image (fastWord b hb o i.val) = retained b A i.val := by
  ext z
  simp only [Finset.mem_image,keep,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact hj
  · intro hz
    obtain ⟨j,rfl⟩ := (fastWord_range b hb o i.val z).mpr (Finset.mem_inter.mp hz).1
    exact ⟨j,hz,rfl⟩

lemma keep_card (i : A) : (keep b hb o A i).card = (retained b A i.val).card := by
  rw [← keep_image b hb o A i,Finset.card_image_of_injective _ (fastWord_injective b hb o i.val)]

variable (hretained : ∀ i : A, 2 ≤ (retained b A i.val).card)

include hretained in
lemma keep_lower (i : A) : 2 ≤ (keep b hb o A i).card := by
  rw [keep_card]
  exact hretained i

def wordEmbedding (i : A) : Fin (arity b i.val+2) ↪ Fin ((l*l)*2) :=
  ⟨fastWord b hb o i.val,fastWord_injective b hb o i.val⟩

lemma removed_private (i : A) (f : Fin (arity b i.val+2)) (hf : f ∉ keep b hb o A i)
    (j : A) (hji : j ≠ i) (g : Fin (arity b j.val+2)) :
    wordEmbedding b hb o A j g ≠ wordEmbedding b hb o A i f := by
  intro h
  apply hf
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,Finset.mem_inter.mpr ⟨fastWord_mem b hb o i.val f,?_⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨j.val,Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h),j.property⟩,?_⟩
  have hg := fastWord_mem b hb o j.val g
  change fastWord b hb o j.val g = fastWord b hb o i.val f at h
  rwa [h] at hg

def coarseSource : (Σ i : A, Fin (WordCoarsening.arity (keep b hb o A) i+2)) → Fin ((l*l)*2) :=
  WordCoarsening.coarseSource (wordEmbedding b hb o A) (keep b hb o A) (keep_lower b hb o A hretained)

def coarseTarget : (Σ i : A, Fin (WordCoarsening.arity (keep b hb o A) i+2)) → Fin ((l*l)*2) :=
  WordCoarsening.coarseTarget (wordEmbedding b hb o A) (keep b hb o A) (keep_lower b hb o A hretained)

lemma spectrum (hsmall : ∀ i : A, arity b i.val ≤ 4) (P : ℕ → Prop) :
    (∃ D, Partition (code (source b hb o) (target b hb o))
      (PathSubstitution.Family.colorLabels A) D ∧ P D.card) ↔
    (∃ D, Partition (code (coarseSource b hb o A hretained) (coarseTarget b hb o A hretained))
      Finset.univ D ∧ P D.card) := by
  have hr := WordKernel.restriction_spectrum (fastWord b hb o) A P
  have hc := WordCoarsening.spectrum_of_le_six (wordEmbedding b hb o A) (keep b hb o A)
    (keep_lower b hb o A hretained) (removed_private b hb o A) hsmall P
  have hs : source b hb o = WordKernel.source (fastWord b hb o) := source_eq_fast b hb o
  have ht : target b hb o = WordKernel.target (fastWord b hb o) := target_eq_fast b hb o
  rw [hs,ht]
  have hl : PathSubstitution.Family.colorLabels (m := fun i => arity b i+2) A =
      Finset.univ.filter (fun e : Σ i, Fin (arity b i+2) => e.1 ∈ A) := by
    ext e
    simp [PathSubstitution.Family.colorLabels]
  rw [hl]
  exact hr.trans hc

#print axioms spectrum
end Erdos184Work.CanonicalSubsetCoarsening
