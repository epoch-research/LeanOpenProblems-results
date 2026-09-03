import Submission.FiveProjection01
import Submission.FiveRows0

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.FiveProjectionCode01
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction FiveProjection01
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 3 → ℕ := ![1,1,1]
lemma row0 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 1 (smallOrder0 q)).vertex =
      FourRows2.words0 (FourRows2.key0 (smallOrder0 q)) →
    enc0 (FiveRows0.key0 q) = (FourRows2.key0 (smallOrder0 q)).val + 1 := by decide +kernel

def enc1 : Fin 3 → ℕ := ![1,1,1]
lemma row1 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 1 (smallOrder1 q)).vertex =
      FourRows2.words1 (FourRows2.key1 (smallOrder1 q)) →
    enc1 (FiveRows0.key2 q) = (FourRows2.key1 (smallOrder1 q)).val + 1 := by decide +kernel

def enc2 : Fin 3 → ℕ := ![1,1,1]
lemma row2 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 1 (smallOrder2 q)).vertex =
      FourRows2.words2 (FourRows2.key2 (smallOrder2 q)) →
    enc2 (FiveRows0.key3 q) = (FourRows2.key2 (smallOrder2 q)).val + 1 := by decide +kernel

def enc3 : Fin 3 → ℕ := ![1,1,1]
lemma row3 : ∀ q : Marked.Order 2,
    (SmallOrderNormalization.normalized 1 (smallOrder3 q)).vertex =
      FourRows2.words3 (FourRows2.key3 (smallOrder3 q)) →
    enc3 (FiveRows0.key4 q) = (FourRows2.key3 (smallOrder3 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,1,1,1)}
def Compatible (q0 : Fin 3) (q1 : Fin 3) (q2 : Fin 3) (q3 : Fin 3) (q4 : Fin 3) : Prop :=
  (enc0 q0,enc1 q2,enc2 q3,enc3 q4) ∈ goodCodes
instance (q0 : Fin 3) (q1 : Fin 3) (q2 : Fin 3) (q3 : Fin 3) (q4 : Fin 3) : Decidable (Compatible q0 q1 q2 q3 q4) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

lemma codes_of_good : ∀ j : Fin 1, j ∈ FourRows2.good →
    ((FourRows2.digit0 j.val).val + 1,(FourRows2.digit1 j.val).val + 1,(FourRows2.digit2 j.val).val + 1,(FourRows2.digit3 j.val).val + 1) ∈ goodCodes := by decide +kernel

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (FiveRows0.key0 (o 0)) (FiveRows0.key1 (o 1)) (FiveRows0.key2 (o 2)) (FiveRows0.key3 (o 3)) (FiveRows0.key4 (o 4)) := by
  have hs := FiveProjection01.localBounds o h
  have hc := codes_of_good ⟨FourRows2.key (smallOrders o),FourRows2.key_lt (smallOrders o)⟩
    (FiveProjection01.catalogue o h)
  rw [FourRows2.digit_key0,FourRows2.digit_key1,FourRows2.digit_key2,FourRows2.digit_key3] at hc
  have hr0 := FourRows2.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 0) hr0
  have hr1 := FourRows2.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 2) hr1
  have hr2 := FourRows2.chosen2 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr2
  have he2 := row2 (o 3) hr2
  have hr3 := FourRows2.chosen3 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr3
  have he3 := row3 (o 4) hr3
  unfold Compatible
  rw [he0,he1,he2,he3]
  simpa only [smallOrders,Fin.cases_zero,Fin.cases_succ] using hc

#print axioms compatible
end Erdos184Work.FiveProjectionCode01
