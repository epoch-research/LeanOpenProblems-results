import Submission.CanonicalPairKernel

/-! Kernel-reducible canonical placements, obtained by filtering the already
ordered list of all finite slots rather than evaluating well-founded merge sort. -/
namespace Erdos184Work.CanonicalPairLayout
open PairJunctionCoding PairSlotMarkers CycleSegments
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3)

def markerList (i : Fin l) : List (Fin ((l*l)*2)) :=
  (List.finRange ((l*l)*2)).filter (fun z => decide (z ∈ markers b i))

@[simp] lemma mem_markerList (i : Fin l) (z : Fin ((l*l)*2)) :
    z ∈ markerList b i ↔ z ∈ markers b i := by simp [markerList]

lemma markerList_toFinset (i : Fin l) : (markerList b i).toFinset = markers b i := by
  ext z
  simp

lemma markerList_sorted (i : Fin l) : (markerList b i).SortedLT := by
  apply List.sortedLT_iff_pairwise.mpr
  exact List.Pairwise.filter _ (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange _))

lemma markerList_length (i : Fin l) : (markerList b i).length = (markers b i).card := by
  rw [← List.toFinset_card_of_nodup (markerList_sorted b i).nodup,markerList_toFinset]

variable (hb : ∀ i, 2 ≤ (markers b i).card)

def fastPlace (i : Fin l) (j : Fin (arity b i+2)) : Fin ((l*l)*2) :=
  (markerList b i).get ⟨j.val,by
    rw [markerList_length]
    have h := j.isLt
    have hc := Nat.sub_add_cancel (hb i)
    change j.val < (markers b i).card - 2 + 2 at h
    omega⟩

lemma fastPlace_mem (i : Fin l) (j : Fin (arity b i+2)) : fastPlace b hb i j ∈ markers b i :=
  (mem_markerList b i _).mp ((markerList b i).get_mem _)

lemma fastPlace_strictMono (i : Fin l) : StrictMono (fastPlace b hb i) := by
  intro j k hjk
  exact (markerList_sorted b i).strictMono_get hjk

lemma place_eq_fast : place b hb = fastPlace b hb := by
  funext i
  exact (Finset.orderEmbOfFin_unique (Nat.sub_add_cancel (hb i)).symm
    (fastPlace_mem b hb i) (fastPlace_strictMono b hb i)).symm

#print axioms place_eq_fast
end Erdos184Work.CanonicalPairLayout

namespace Erdos184Work.CanonicalPairKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
    (o : ∀ i, Marked.Order (arity b i))

def fastSource : (Σ i, Fin (arity b i+2)) → Fin ((l*l)*2) :=
  NormalizedKernel.src (fastPlace b hb) o

def fastTarget : (Σ i, Fin (arity b i+2)) → Fin ((l*l)*2) :=
  NormalizedKernel.dst (fastPlace b hb) o

lemma source_eq_fast : source b hb o = fastSource b hb o := by
  unfold source fastSource
  rw [place_eq_fast]

lemma target_eq_fast : target b hb o = fastTarget b hb o := by
  unfold target fastTarget
  rw [place_eq_fast]

#print axioms source_eq_fast
end Erdos184Work.CanonicalPairKernel
