import Submission.FiniteIntervals
import Submission.SixProjection02
import Submission.SixRows0
import Submission.FiveWordOrbits0

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.SixProjectionCode02
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection02
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 12 → ℕ := ![1,2,3,2,3,1,1,2,1,2,3,3]
lemma row0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 q)).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 q)) →
    enc0 (SixRows0.key0 q) = (FiveRows0.key0 (smallOrder0 q)).val + 1 := by decide +kernel

def enc1 : Fin 12 → ℕ := ![1,2,3,2,3,1,1,2,1,2,3,3]
lemma row1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 q)).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 q)) →
    enc1 (SixRows0.key1 q) = (FiveRows0.key1 (smallOrder1 q)).val + 1 := by decide +kernel

def enc2 : Fin 12 → ℕ := ![1,2,1,1,2,2,1,2,3,3,3,3]
lemma row2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex =
      FiveRows0.words2 (FiveRows0.key2 (smallOrder2 q)) →
    enc2 (SixRows0.key3 q) = (FiveRows0.key2 (smallOrder2 q)).val + 1 := by decide +kernel

def enc3 : Fin 12 → ℕ := ![1,2,1,1,2,2,1,2,3,3,3,3]
lemma row3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex =
      FiveRows0.words3 (FiveRows0.key3 (smallOrder3 q)) →
    enc3 (SixRows0.key4 q) = (FiveRows0.key3 (smallOrder3 q)).val + 1 := by decide +kernel

def enc4 : Fin 12 → ℕ := ![1,2,1,1,2,2,1,2,3,3,3,3]
lemma row4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows0.words4 (FiveRows0.key4 (smallOrder4 q)) →
    enc4 (SixRows0.key5 q) = (FiveRows0.key4 (smallOrder4 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,1,1,1,3),(1,1,1,2,1),(1,1,1,2,3),(1,1,2,1,2),(1,1,2,1,3),(1,1,2,2,3),(1,1,3,1,1),(1,1,3,1,2),(1,1,3,1,3),(1,1,3,2,1),(1,1,3,2,2),(1,1,3,2,3),(1,2,1,1,1),(1,2,1,1,2),(1,2,1,1,3),(1,2,1,2,1),(1,2,1,2,2),(1,2,1,2,3),(1,2,1,3,1),(1,2,1,3,2),(1,2,1,3,3),(1,2,2,1,2),(1,2,2,1,3),(1,2,2,3,2),(1,2,3,1,1),(1,2,3,1,2),(1,2,3,1,3),(1,2,3,2,1),(1,2,3,2,2),(1,2,3,2,3),(1,2,3,3,1),(1,2,3,3,2),(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
def Compatible (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Prop :=
  (enc0 q0,enc1 q1,enc2 q3,enc3 q4,enc4 q5) ∈ goodCodes
instance (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Decidable (Compatible q0 q1 q2 q3 q4 q5) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

/- Direct catalogue insertion proofs avoid evaluating nested finset deduplication. -/
/- Factored catalogue insertion proofs avoid repeated long prefixes. -/
def CodesIndex (j : ℕ) : Prop := ∀ hj : j < 156,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨j,hj⟩).val).val + 1) ∈ goodCodes
def codeSuffix00 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := goodCodes
lemma codeSuffix00_subset : codeSuffix00 ⊆ goodCodes := by
  intro x hx
  exact hx
def codeSuffix01 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,2,1,2,2),(1,2,1,2,3),(1,2,1,3,1),(1,2,1,3,2),(1,2,1,3,3),(1,2,2,1,2),(1,2,2,1,3),(1,2,2,3,2),(1,2,3,1,1),(1,2,3,1,2),(1,2,3,1,3),(1,2,3,2,1),(1,2,3,2,2),(1,2,3,2,3),(1,2,3,3,1),(1,2,3,3,2),(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix01_subset : codeSuffix01 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix00_subset
  unfold codeSuffix00 goodCodes
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix02 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix02_subset : codeSuffix02 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix01_subset
  unfold codeSuffix01
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix03 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix03_subset : codeSuffix03 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix02_subset
  unfold codeSuffix02
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix04 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix04_subset : codeSuffix04 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix03_subset
  unfold codeSuffix03
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix05 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix05_subset : codeSuffix05 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix04_subset
  unfold codeSuffix04
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix06 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix06_subset : codeSuffix06 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix05_subset
  unfold codeSuffix05
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix07 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix07_subset : codeSuffix07 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix06_subset
  unfold codeSuffix06
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix08 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix08_subset : codeSuffix08 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix07_subset
  unfold codeSuffix07
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix09 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix09_subset : codeSuffix09 ⊆ goodCodes := by
  intro x hx
  apply codeSuffix08_subset
  unfold codeSuffix08
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
lemma codes_chunk00 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨0+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix00_subset
    change (1,1,1,1,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,1,2,1) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,1,2,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,2,1,2) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,2,1,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,2,2,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,3,1,1) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,3,1,2) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,3,1,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,3,2,1) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,3,2,2) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,1,3,2,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,2,1,1,1) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,2,1,1,2) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,2,1,1,3) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix00_subset
    change (1,2,1,2,1) ∈ codeSuffix00
    unfold codeSuffix00 goodCodes
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval00 : FiniteIntervals.Covers CodesIndex 0 16 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 0 16
  intro i hj
  exact codes_chunk00 i
lemma codes_chunk01 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨16+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix01_subset
    change (1,2,1,2,2) ∈ codeSuffix01
    unfold codeSuffix01
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,1,2,3) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,1,3,1) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,1,3,2) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,1,3,3) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,2,1,2) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,2,1,3) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,2,3,2) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,1,1) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,1,2) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,1,3) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,2,1) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,2,2) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,2,3) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,3,1) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix01_subset
    change (1,2,3,3,2) ∈ codeSuffix01
    unfold codeSuffix01
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval01 : FiniteIntervals.Covers CodesIndex 16 32 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 16 16
  intro i hj
  exact codes_chunk01 i
lemma codes_chunk02 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨32+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix02_subset
    change (1,3,1,1,2) ∈ codeSuffix02
    unfold codeSuffix02
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,1,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,2,1) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,2,2) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,2,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,3,1) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,3,2) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,1,3,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,2,1,2) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,2,1,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,2,2,2) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,2,2,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,2,3,2) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,2,3,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,3,1,2) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix02_subset
    change (1,3,3,1,3) ∈ codeSuffix02
    unfold codeSuffix02
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval02 : FiniteIntervals.Covers CodesIndex 32 48 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 32 16
  intro i hj
  exact codes_chunk02 i
lemma codes_chunk03 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨48+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix03_subset
    change (1,3,3,2,1) ∈ codeSuffix03
    unfold codeSuffix03
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (1,3,3,2,2) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (1,3,3,2,3) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (1,3,3,3,2) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,1,2,1) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,1,2,3) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,1,3,1) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,1,1) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,1,2) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,1,3) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,2,1) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,2,2) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,2,3) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,3,1) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,3,2) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix03_subset
    change (2,1,2,3,3) ∈ codeSuffix03
    unfold codeSuffix03
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval03 : FiniteIntervals.Covers CodesIndex 48 64 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 48 16
  intro i hj
  exact codes_chunk03 i
lemma codes_chunk04 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨64+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix04_subset
    change (2,1,3,1,1) ∈ codeSuffix04
    unfold codeSuffix04
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,1,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,1,3) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,2,1) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,2,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,2,3) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,3,1) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,1,3,3,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,1,2,1) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,1,3,1) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,1,3,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,2,1,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,2,3,1) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,2,3,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,3,1,1) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix04_subset
    change (2,2,3,1,2) ∈ codeSuffix04
    unfold codeSuffix04
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval04 : FiniteIntervals.Covers CodesIndex 64 80 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 64 16
  intro i hj
  exact codes_chunk04 i
lemma codes_chunk05 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨80+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix05_subset
    change (2,2,3,2,1) ∈ codeSuffix05
    unfold codeSuffix05
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,2,3,2,2) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,2,3,3,1) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,2,3,3,2) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,1,2,1) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,1,2,2) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,1,2,3) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,1,3,1) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,1,3,2) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,1,3,3) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,2,1,2) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,2,1,3) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,2,2,1) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,2,2,2) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,2,2,3) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix05_subset
    change (2,3,2,3,1) ∈ codeSuffix05
    unfold codeSuffix05
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval05 : FiniteIntervals.Covers CodesIndex 80 96 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 80 16
  intro i hj
  exact codes_chunk05 i
lemma codes_chunk06 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨96+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix06_subset
    change (2,3,2,3,2) ∈ codeSuffix06
    unfold codeSuffix06
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,2,3,3) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,3,1,2) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,3,2,1) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,3,2,2) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,3,2,3) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,3,3,1) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (2,3,3,3,2) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,1,1,1) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,1,1,3) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,1,2,1) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,1,2,3) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,1,3,1) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,1,3,3) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,2,1,1) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix06_subset
    change (3,1,2,1,2) ∈ codeSuffix06
    unfold codeSuffix06
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval06 : FiniteIntervals.Covers CodesIndex 96 112 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 96 16
  intro i hj
  exact codes_chunk06 i
lemma codes_chunk07 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨112+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix07_subset
    change (3,1,2,1,3) ∈ codeSuffix07
    unfold codeSuffix07
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,2,2,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,2,2,3) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,2,3,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,2,3,2) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,2,3,3) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,3,1,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,3,1,2) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,3,1,3) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,3,2,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,3,2,3) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,1,3,3,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,2,1,1,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,2,1,1,2) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,2,1,1,3) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix07_subset
    change (3,2,1,2,1) ∈ codeSuffix07
    unfold codeSuffix07
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval07 : FiniteIntervals.Covers CodesIndex 112 128 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 112 16
  intro i hj
  exact codes_chunk07 i
lemma codes_chunk08 : ∀ i : Fin 16,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨128+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix08_subset
    change (3,2,1,2,3) ∈ codeSuffix08
    unfold codeSuffix08
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,1,3,1) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,1,3,2) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,1,3,3) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,2,1,1) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,2,1,2) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,2,1,3) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,2,3,1) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,2,3,2) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,2,3,3) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,3,1,1) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,3,1,2) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,3,1,3) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,3,2,1) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,3,3,1) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix08_subset
    change (3,2,3,3,2) ∈ codeSuffix08
    unfold codeSuffix08
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval08 : FiniteIntervals.Covers CodesIndex 128 144 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 128 16
  intro i hj
  exact codes_chunk08 i
lemma codes_chunk09 : ∀ i : Fin 12,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey ⟨144+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · apply codeSuffix09_subset
    change (3,3,1,1,3) ∈ codeSuffix09
    unfold codeSuffix09
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,1,2,1) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,1,2,3) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,1,3,1) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,1,3,2) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,1,3,3) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,2,1,2) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,2,1,3) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,2,2,3) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,2,3,1) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,2,3,2) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · apply codeSuffix09_subset
    change (3,3,2,3,3) ∈ codeSuffix09
    unfold codeSuffix09
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_singleton_self _
lemma codes_interval09 : FiniteIntervals.Covers CodesIndex 144 156 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 144 12
  intro i hj
  exact codes_chunk09 i
lemma codes_valid : ∀ i : FiveWordOrbits0.Cases,
    ((FiveRows0.digit0 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey i).val).val + 1) ∈ goodCodes := by
  intro i
  have hc : FiniteIntervals.Covers CodesIndex 0 156 := (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge codes_interval00 codes_interval01) (FiniteIntervals.merge codes_interval02 (FiniteIntervals.merge codes_interval03 codes_interval04))) (FiniteIntervals.merge (FiniteIntervals.merge codes_interval05 codes_interval06) (FiniteIntervals.merge codes_interval07 (FiniteIntervals.merge codes_interval08 codes_interval09))))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma codes_of_good (j : Fin 243) (hj : j ∈ FiveRows0.good) :
    ((FiveRows0.digit0 j.val).val + 1,(FiveRows0.digit1 j.val).val + 1,(FiveRows0.digit2 j.val).val + 1,(FiveRows0.digit3 j.val).val + 1,(FiveRows0.digit4 j.val).val + 1) ∈ goodCodes := by
  rw [FiveWordOrbits0.good_eq] at hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact codes_valid i

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5)) := by
  have hs := SixProjection02.localBounds o h
  have hc := codes_of_good ⟨FiveRows0.key (smallOrders o),FiveRows0.key_lt (smallOrders o)⟩
    (SixProjection02.catalogue o h)
  rw [FiveRows0.digit_key0,FiveRows0.digit_key1,FiveRows0.digit_key2,FiveRows0.digit_key3,FiveRows0.digit_key4] at hc
  have hr0 := FiveRows0.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 0) hr0
  have hr1 := FiveRows0.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 1) hr1
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
end Erdos184Work.SixProjectionCode02
