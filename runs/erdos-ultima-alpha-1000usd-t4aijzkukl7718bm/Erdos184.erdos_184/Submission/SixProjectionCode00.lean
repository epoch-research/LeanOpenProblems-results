import Submission.SixProjection00
import Submission.SixRows0
import Submission.FiveWordOrbits0

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.SixProjectionCode00
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection00
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 q)).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 q)) →
    enc0 (SixRows0.key1 q) = (FiveRows0.key0 (smallOrder0 q)).val + 1 := by decide +kernel

def enc1 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 q)).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 q)) →
    enc1 (SixRows0.key2 q) = (FiveRows0.key1 (smallOrder1 q)).val + 1 := by decide +kernel

def enc2 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex =
      FiveRows0.words2 (FiveRows0.key2 (smallOrder2 q)) →
    enc2 (SixRows0.key3 q) = (FiveRows0.key2 (smallOrder2 q)).val + 1 := by decide +kernel

def enc3 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex =
      FiveRows0.words3 (FiveRows0.key3 (smallOrder3 q)) →
    enc3 (SixRows0.key4 q) = (FiveRows0.key3 (smallOrder3 q)).val + 1 := by decide +kernel

def enc4 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows0.words4 (FiveRows0.key4 (smallOrder4 q)) →
    enc4 (SixRows0.key5 q) = (FiveRows0.key4 (smallOrder4 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,1,1,1,3),(1,1,1,2,1),(1,1,1,2,3),(1,1,2,1,2),(1,1,2,1,3),(1,1,2,2,3),(1,1,3,1,1),(1,1,3,1,2),(1,1,3,1,3),(1,1,3,2,1),(1,1,3,2,2),(1,1,3,2,3),(1,2,1,1,1),(1,2,1,1,2),(1,2,1,1,3),(1,2,1,2,1),(1,2,1,2,2),(1,2,1,2,3),(1,2,1,3,1),(1,2,1,3,2),(1,2,1,3,3),(1,2,2,1,2),(1,2,2,1,3),(1,2,2,3,2),(1,2,3,1,1),(1,2,3,1,2),(1,2,3,1,3),(1,2,3,2,1),(1,2,3,2,2),(1,2,3,2,3),(1,2,3,3,1),(1,2,3,3,2),(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
def Compatible (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Prop :=
  (enc0 q1,enc1 q2,enc2 q3,enc3 q4,enc4 q5) ∈ goodCodes
instance (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Decidable (Compatible q0 q1 q2 q3 q4 q5) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

lemma codes_valid : ∀ i : FiveWordOrbits0.Cases,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey i).val).val + 1) ∈ goodCodes := by decide +kernel

lemma codes_of_good (j : Fin 243) (hj : j ∈ FiveRows0.good) :
    ((FiveRows0.digit0 j.val).val + 1,(FiveRows0.digit1 j.val).val + 1,(FiveRows0.digit2 j.val).val + 1,(FiveRows0.digit3 j.val).val + 1,(FiveRows0.digit4 j.val).val + 1) ∈ goodCodes := by
  rw [FiveWordOrbits0.good_eq] at hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact codes_valid i

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5)) := by
  have hs := SixProjection00.localBounds o h
  have hc := codes_of_good ⟨FiveRows0.key (smallOrders o),FiveRows0.key_lt (smallOrders o)⟩
    (SixProjection00.catalogue o h)
  rw [FiveRows0.digit_key0,FiveRows0.digit_key1,FiveRows0.digit_key2,FiveRows0.digit_key3,FiveRows0.digit_key4] at hc
  have hr0 := FiveRows0.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 1) hr0
  have hr1 := FiveRows0.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 2) hr1
  have hr2 := FiveRows0.chosen2 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr2
  have he2 := row2 (o 3) hr2
  have hr3 := FiveRows0.chosen3 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr3
  have he3 := row3 (o 4) hr3
  have hr4 := FiveRows0.chosen4 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr4
  have he4 := row4 (o 5) hr4
  unfold Compatible
  rw [he0,he1,he2,he3,he4]
  simpa only [smallOrders,Fin.cases_zero,Fin.cases_succ] using hc

#print axioms compatible
end Erdos184Work.SixProjectionCode00
