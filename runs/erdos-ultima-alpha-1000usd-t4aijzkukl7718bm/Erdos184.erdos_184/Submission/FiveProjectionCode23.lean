import Submission.FiveProjection23
import Submission.FiveRows2

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.FiveProjectionCode23
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction FiveProjection23
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 3 → ℕ := ![1,1,1]
lemma row0 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 1 (smallOrder0 q)).vertex =
      FourRows4.words0 (FourRows4.key0 (smallOrder0 q)) →
    enc0 (FiveRows2.key4 q) = (FourRows4.key0 (smallOrder0 q)).val + 1 := by decide +kernel

def enc1 : Fin 12 → ℕ := ![2,2,2,1,1,1,3,3,3,1,2,3]
lemma row1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 q)).vertex =
      FourRows4.words1 (FourRows4.key1 (smallOrder1 q)) →
    enc1 (FiveRows2.key1 q) = (FourRows4.key1 (smallOrder1 q)).val + 1 := by decide +kernel

def enc2 : Fin 12 → ℕ := ![2,2,2,1,1,1,3,3,3,1,2,3]
lemma row2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex =
      FourRows4.words2 (FourRows4.key2 (smallOrder2 q)) →
    enc2 (FiveRows2.key2 q) = (FourRows4.key2 (smallOrder2 q)).val + 1 := by decide +kernel

def enc3 : Fin 60 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,3,3,3,0,0,0,0,1,3,0,4,4,4,0,4,2,2,2,4,0,0,0,0,2,0,3,0,0,0,1,0,2,0]
lemma row3 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder3 q)).vertex =
      FourRows4.words3 (FourRows4.key3 (smallOrder3 q)) →
    enc3 (FiveRows2.key0 q) = (FourRows4.key3 (smallOrder3 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,1,1,2),(1,1,2,1),(1,1,3,1),(1,1,3,2),(1,2,1,4),(1,2,2,3),(1,2,3,3),(1,2,3,4),(1,3,1,2),(1,3,1,4),(1,3,2,1),(1,3,2,3)}
def Compatible (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 3) (q4 : Fin 3) : Prop :=
  (enc0 q4,enc1 q1,enc2 q2,enc3 q0) ∈ goodCodes
instance (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 3) (q4 : Fin 3) : Decidable (Compatible q0 q1 q2 q3 q4) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

lemma codes_of_good : ∀ j : Fin 36, j ∈ FourRows4.good →
    ((FourRows4.digit0 j.val).val + 1,(FourRows4.digit1 j.val).val + 1,(FourRows4.digit2 j.val).val + 1,(FourRows4.digit3 j.val).val + 1) ∈ goodCodes := by decide +kernel

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (FiveRows2.key0 (o 0)) (FiveRows2.key1 (o 1)) (FiveRows2.key2 (o 2)) (FiveRows2.key3 (o 3)) (FiveRows2.key4 (o 4)) := by
  have hs := FiveProjection23.localBounds o h
  have hc := codes_of_good ⟨FourRows4.key (smallOrders o),FourRows4.key_lt (smallOrders o)⟩
    (FiveProjection23.catalogue o h)
  rw [FourRows4.digit_key0,FourRows4.digit_key1,FourRows4.digit_key2,FourRows4.digit_key3] at hc
  have hr0 := FourRows4.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 4) hr0
  have hr1 := FourRows4.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 1) hr1
  have hr2 := FourRows4.chosen2 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr2
  have he2 := row2 (o 2) hr2
  have hr3 := FourRows4.chosen3 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr3
  have he3 := row3 (o 0) hr3
  unfold Compatible
  rw [he0,he1,he2,he3]
  simpa only [smallOrders,Fin.cases_zero,Fin.cases_succ] using hc

#print axioms compatible
end Erdos184Work.FiveProjectionCode23
