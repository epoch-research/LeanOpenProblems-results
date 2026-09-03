import Submission.StableCanonicalCoarsening

/-! Pointwise locality of canonical cyclic rows. This lets finite endpoint
checks enumerate one order at a time, rather than an entire dependent tuple. -/
namespace Erdos184Work.LocalCanonicalRows
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel CanonicalSubsetCoarsening
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

def firstMarker : (n : ℕ) → Marked.Marker n
  | 0 => (0 : Fin 2)
  | n+1 => Sum.inl (firstMarker n)
def defaultOrder : (n : ℕ) → Marked.Order n
  | 0 => ()
  | n+1 => (defaultOrder n,firstMarker n)

variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o o' : ∀ i, Marked.Order (arity b i))

lemma fastWord_congr (i : Fin l) (h : o i = o' i) :
    fastWord b hb o i = fastWord b hb o' i := by
  funext j
  unfold fastWord
  rw [h]

lemma keep_congr (A : Finset (Fin l)) (i : A) (h : o i.val = o' i.val) :
    keep b hb o A i = keep b hb o' A i := by
  unfold keep
  rw [fastWord_congr b hb o o' i.val h]

lemma cyclicVertex_congr {n : ℕ} {s t : Finset (Fin (n+2))}
    (hs : 2 ≤ s.card) (ht : 2 ≤ t.card) (he : s = t)
    (i : Fin (CyclicSeries.arity s+2)) (j : Fin (CyclicSeries.arity t+2))
    (hij : i.val = j.val) : CyclicSeries.vertex s hs i = CyclicSeries.vertex t ht j := by
  subst t
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma stableWord_congr (A : Finset (Fin l))
    (hretained : ∀ i : A, 2 ≤ (retained b A i.val).card)
    (i : A) (h : o i.val = o' i.val) (j : Fin (StableCanonicalCoarsening.arity b A i+2)) :
    StableCanonicalCoarsening.word b hb o A hretained i j =
      StableCanonicalCoarsening.word b hb o' A hretained i j := by
  change fastWord b hb o i.val (CyclicSeries.vertex (keep b hb o A i)
      (keep_lower b hb o A hretained i) (StableCanonicalCoarsening.index b hb o A i j)) =
    fastWord b hb o' i.val (CyclicSeries.vertex (keep b hb o' A i)
      (keep_lower b hb o' A hretained i) (StableCanonicalCoarsening.index b hb o' A i j))
  have hjv : (StableCanonicalCoarsening.index b hb o A i j).val =
      (StableCanonicalCoarsening.index b hb o' A i j).val := by
    simp only [StableCanonicalCoarsening.index,finCongr_apply_coe]
  have hv := cyclicVertex_congr (n := arity b i.val)
    (s := keep b hb o A i) (t := keep b hb o' A i)
    (keep_lower b hb o A hretained i)
    (keep_lower b hb o' A hretained i) (keep_congr b hb o o' A i h)
    (StableCanonicalCoarsening.index b hb o A i j) (StableCanonicalCoarsening.index b hb o' A i j) hjv
  rw [fastWord_congr b hb o o' i.val h,hv]

variable (i : Fin l) (q : Marked.Order (arity b i))

def oneOrder : ∀ j, Marked.Order (arity b j) :=
  Function.update (fun j => defaultOrder (arity b j)) i q

lemma oneOrder_self : oneOrder b i q i = q := Function.update_self ..

lemma stableWord_local (A : Finset (Fin l))
    (hretained : ∀ i : A, 2 ≤ (retained b A i.val).card)
    (i : A) (j : Fin (StableCanonicalCoarsening.arity b A i+2)) :
    StableCanonicalCoarsening.word b hb o A hretained i j =
      StableCanonicalCoarsening.word b hb (oneOrder b i.val (o i.val)) A hretained i j := by
  apply stableWord_congr
  exact (oneOrder_self b i.val (o i.val)).symm

#print axioms stableWord_local
end Erdos184Work.LocalCanonicalRows
