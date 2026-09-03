import Submission.FlatCanonicalKernel

/-! Exact finite rejection certificates for the four-color double-square
contact pattern: multiplicities (0,2,2,2,2,0). -/
namespace Erdos184Work.FourDoubleSquareKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000
set_option Elab.async false

def counts (p : PairIndex 4) : Fin 3 :=
  if (p.val.1 = 0 ∧ p.val.2 = 1) ∨ (p.val.1 = 2 ∧ p.val.2 = 3) then 0 else 2
lemma marker_bound : ∀ i, 2 ≤ (markers counts i).card := by decide +kernel
lemma arity_two : ∀ i, arity counts i = 2 := by decide +kernel

lemma size_eq : FlatCanonicalKernel.size counts = 16 := by decide +kernel
instance : NeZero (FlatCanonicalKernel.size counts) := ⟨by rw [size_eq]; decide⟩
abbrev E := Fin 16
abbrev W := Fin 32
abbrev Orders := ∀ i : Fin 4, Marked.Order (arity counts i)

def localIndex (i : Fin 4) (o : Orders) : ℕ :=
  let v := (SmallOrderNormalization.normalized (arity counts i) (o i)).vertex
  if (v 1).val = 2 then 2 else if (v 2).val = 2 then 0 else 1

def key (o : Orders) : ℕ := 27 * localIndex 0 o + 9 * localIndex 1 o + 3 * localIndex 2 o + localIndex 3 o

def color (e : E) : Fin 4 := ⟨e.val / 4,by omega⟩

def src0 : E → W := ![4,5,6,7,12,13,14,15,4,5,12,13,6,7,14,15]
def dst0 : E → W := ![5,6,7,4,13,14,15,12,5,12,13,4,7,14,15,6]

def data0 : RejectionData E W (Fin 4) := .rigid {0,2,3} {
  size := 12
  edge := ![0,1,2,3,8,9,10,11,12,13,14,15]
  series := {
    fiber := ![0,1,2,3,4,5,5,5,6,7,7,7]
    representative := ![0,1,2,3,4,5,8,9]
    vertex := ![4,5,6,7]
    rank := ![0,0,0,0,0,0,1,2,0,0,1,2]
    parent := ![0,1,2,3,4,5,5,6,8,9,9,10]
    link := ![4,5,6,7,4,5,12,13,6,7,14,15] } }


lemma valid0 : data0.Valid src0 dst0 color := by decide +kernel
#print axioms valid0
end Erdos184Work.FourDoubleSquareKernel
