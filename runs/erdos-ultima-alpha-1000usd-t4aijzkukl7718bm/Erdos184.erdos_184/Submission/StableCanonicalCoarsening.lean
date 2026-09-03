import Submission.CanonicalSubsetCoarsening

/-! A word-size-stable presentation of canonical color restriction. The
coarse label sizes depend only on the contact counts and selected colors,
not on their cyclic orders. -/
open scoped Classical
namespace Erdos184Work.StableCanonicalCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (CanonicalPairLayout.arity b i)) (A : Finset (Fin l))
  (hretained : ∀ i : A, 2 ≤ (retained b A i.val).card)

noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

def arity (i : A) : ℕ := (retained b A i.val).card - 2

lemma arity_eq (i : A) : arity b A i = WordCoarsening.arity (keep b hb o A) i := by
  unfold arity WordCoarsening.arity CyclicSeries.arity
  rw [keep_card]

def index (i : A) : Fin (arity b A i+2) ≃ Fin (WordCoarsening.arity (keep b hb o A) i+2) :=
  finCongr (congrArg (· + 2) (arity_eq b hb o A i))

lemma index_next (i : A) (j : Fin (arity b A i+2)) :
    index b hb o A i (j+1) = index b hb o A i j + 1 := by
  have aux {a c : ℕ} (h : a = c) (j : Fin (a+2)) :
      finCongr (congrArg (·+2) h) (j+1) = finCongr (congrArg (·+2) h) j+1 := by
    subst c
    rfl
  exact aux (arity_eq b hb o A i) j

def word (i : A) (j : Fin (arity b A i+2)) : Fin ((l*l)*2) :=
  WordCoarsening.coarseWord (wordEmbedding b hb o A) (keep b hb o A)
    (keep_lower b hb o A hretained) i (index b hb o A i j)

def source (e : Σ i : A, Fin (arity b A i+2)) : Fin ((l*l)*2) := word b hb o A hretained e.1 e.2
def target (e : Σ i : A, Fin (arity b A i+2)) : Fin ((l*l)*2) := word b hb o A hretained e.1 (e.2+1)

def edgeEquiv : (Σ i : A, Fin (arity b A i+2)) ≃
    (Σ i : A, Fin (WordCoarsening.arity (keep b hb o A) i+2)) :=
  Equiv.sigmaCongrRight (index b hb o A)

def embedding : Embedding (source b hb o A hretained) (target b hb o A hretained)
    (CanonicalSubsetCoarsening.coarseSource b hb o A hretained)
    (CanonicalSubsetCoarsening.coarseTarget b hb o A hretained) where
  edge := (edgeEquiv b hb o A).toEmbedding
  vertex := Function.Embedding.refl _
  endpoints e := by
    change s(word b hb o A hretained e.1 e.2,word b hb o A hretained e.1 (e.2+1)) = _
    unfold word
    rw [index_next]
    rfl

lemma map_univ : (Finset.univ : Finset (Σ i : A, Fin (arity b A i+2))).map
    (embedding b hb o A hretained).edge = Finset.univ :=
  Finset.map_univ_equiv (edgeEquiv b hb o A)

lemma spectrum (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 4) (P : ℕ → Prop) :
    (∃ D, Partition (code (CanonicalPairKernel.source b hb o) (CanonicalPairKernel.target b hb o))
      (PathSubstitution.Family.colorLabels A) D ∧ P D.card) ↔
    (∃ D, Partition (code (source b hb o A hretained) (target b hb o A hretained))
      Finset.univ D ∧ P D.card) := by
  let M := embedding b hb o A hretained
  let T := SupportTransport.ofEmbedding M.edge M.valid_map
  have h := T.exists_partition_card_iff Finset.univ P
  change (∃ D, Partition _ (Finset.univ.map M.edge) D ∧ P D.card) ↔ _ at h
  rw [map_univ] at h
  exact (CanonicalSubsetCoarsening.spectrum b hb o A hretained hsmall P).trans h

#print axioms spectrum
end Erdos184Work.StableCanonicalCoarsening
