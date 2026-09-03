import Submission.StableCanonicalCoarsening

/-! Suppression is literally filtering a cyclic vertex word. A total list
lookup exposes this fact without dependent bound proofs in finite checks. -/
namespace Erdos184Work.LabelKernel.FilteredWord
set_option maxHeartbeats 1000000
variable {X : Type*} [DecidableEq X] {n : ℕ}
  (word : Fin (n+2) → X) (s : Finset X)

def selected : Finset (Fin (n+2)) := Finset.univ.filter (fun j => word j ∈ s)
def filtered : List X := ((List.finRange (n+2)).map word).filter (fun x => decide (x ∈ s))

lemma kept_map : (CyclicSeries.kept (selected word s)).map word = filtered word s := by
  unfold CyclicSeries.kept selected filtered
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro j _
  simp

lemma length : (filtered word s).length = (selected word s).card := by
  rw [← kept_map,List.length_map,CyclicSeries.kept_length]

lemma vertex_eq_getD (hs : 2 ≤ (selected word s).card)
    (j : Fin (CyclicSeries.arity (selected word s)+2)) (d : X) :
    word (CyclicSeries.vertex (selected word s) hs j) = (filtered word s).getD j.val d := by
  have hj : j.val < ((CyclicSeries.kept (selected word s)).map word).length := by
    rw [List.length_map,CyclicSeries.kept_length]
    have hj := j.isLt
    have ha := CyclicSeries.arity_add (selected word s) hs
    omega
  rw [← kept_map,List.getD_eq_getElem _ _ hj]
  simp only [List.getElem_map,CyclicSeries.vertex,List.get_eq_getElem]

#print axioms vertex_eq_getD
end Erdos184Work.LabelKernel.FilteredWord

namespace Erdos184Work.StableCanonicalCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel CanonicalSubsetCoarsening
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (CanonicalPairLayout.arity b i)) (A : Finset (Fin l))
  (hretained : ∀ i : A, 2 ≤ (retained b A i.val).card)

lemma word_eq_getD (i : A) (j : Fin (arity b A i+2)) (d : Fin ((l*l)*2)) :
    word b hb o A hretained i j =
      (FilteredWord.filtered (fastWord b hb o i.val) (retained b A i.val)).getD j.val d := by
  exact FilteredWord.vertex_eq_getD (fastWord b hb o i.val) (retained b A i.val)
    (keep_lower b hb o A hretained i) (index b hb o A i j) d

#print axioms word_eq_getD
end Erdos184Work.StableCanonicalCoarsening
