import Submission.FiniteIntervals
import Submission.SixProjection40
import Submission.SixRows4
import Submission.FiveWordOrbits0

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.SixProjectionCode40
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection40
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 60 → ℕ := ![1,2,3,2,3,1,2,1,3,1,3,2,2,3,1,3,1,2,1,3,2,3,2,1,1,2,3,2,3,1,1,2,1,2,3,2,3,2,3,1,3,1,2,1,3,3,2,1,2,1,3,3,3,3,2,1,2,2,1,1]
lemma row0_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc0 (SixRows4.key1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row0_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc0 (SixRows4.key1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row0_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key1 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key1 (q,(Sum.inl (Sum.inr ())))) = (FiveRows0.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder0 (q,(Sum.inr ())))).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 (q,(Sum.inr ())))) →
    enc0 (SixRows4.key1 (q,(Sum.inr ()))) = (FiveRows0.key0 (smallOrder0 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 2 (smallOrder0 q)).vertex =
      FiveRows0.words0 (FiveRows0.key0 (smallOrder0 q)) →
    enc0 (SixRows4.key1 q) = (FiveRows0.key0 (smallOrder0 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0 q
  · exact row0_1 q
  · exact row0_2 q
  · exact row0_3 q
  · exact row0_4 q

def enc1 : Fin 60 → ℕ := ![1,2,3,2,3,1,2,1,3,1,3,2,2,3,1,3,1,2,1,3,2,3,2,1,1,2,3,2,3,1,1,2,1,2,3,2,3,2,3,1,3,1,2,1,3,3,2,1,2,1,3,3,3,3,2,1,2,2,1,1]
lemma row1_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row1_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inr ())))) = (FiveRows0.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row1_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder1 (q,(Sum.inr ())))).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 (q,(Sum.inr ())))) →
    enc1 (SixRows4.key2 (q,(Sum.inr ()))) = (FiveRows0.key1 (smallOrder1 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row1 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 2 (smallOrder1 q)).vertex =
      FiveRows0.words1 (FiveRows0.key1 (smallOrder1 q)) →
    enc1 (SixRows4.key2 q) = (FiveRows0.key1 (smallOrder1 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row1_0 q
  · exact row1_1 q
  · exact row1_2 q
  · exact row1_3 q
  · exact row1_4 q

def enc2 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex =
      FiveRows0.words2 (FiveRows0.key2 (smallOrder2 q)) →
    enc2 (SixRows4.key3 q) = (FiveRows0.key2 (smallOrder2 q)).val + 1 := by decide +kernel

def enc3 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex =
      FiveRows0.words3 (FiveRows0.key3 (smallOrder3 q)) →
    enc3 (SixRows4.key4 q) = (FiveRows0.key3 (smallOrder3 q)).val + 1 := by decide +kernel

def enc4 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
lemma row4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows0.words4 (FiveRows0.key4 (smallOrder4 q)) →
    enc4 (SixRows4.key5 q) = (FiveRows0.key4 (smallOrder4 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,1,1,1,3),(1,1,1,2,1),(1,1,1,2,3),(1,1,2,1,2),(1,1,2,1,3),(1,1,2,2,3),(1,1,3,1,1),(1,1,3,1,2),(1,1,3,1,3),(1,1,3,2,1),(1,1,3,2,2),(1,1,3,2,3),(1,2,1,1,1),(1,2,1,1,2),(1,2,1,1,3),(1,2,1,2,1),(1,2,1,2,2),(1,2,1,2,3),(1,2,1,3,1),(1,2,1,3,2),(1,2,1,3,3),(1,2,2,1,2),(1,2,2,1,3),(1,2,2,3,2),(1,2,3,1,1),(1,2,3,1,2),(1,2,3,1,3),(1,2,3,2,1),(1,2,3,2,2),(1,2,3,2,3),(1,2,3,3,1),(1,2,3,3,2),(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
def Compatible (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Prop :=
  (enc0 q1,enc1 q2,enc2 q3,enc3 q4,enc4 q5) ∈ goodCodes
instance (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Decidable (Compatible q0 q1 q2 q3 q4 q5) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

/- Direct catalogue insertion proofs avoid evaluating nested finset deduplication. -/
/- Factored catalogue insertion proofs avoid repeated long prefixes. -/
/- Opaque-index catalogue assembly; value equalities are checked separately. -/
def CodesValue (i : FiveWordOrbits0.Cases) : (ℕ × ℕ × ℕ × ℕ × ℕ) := ((FiveRows0.digit0 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey i).val).val + 1)
def CodesAt (i : FiveWordOrbits0.Cases) : Prop := CodesValue i ∈ goodCodes
def CodesIndex (j : ℕ) : Prop := ∀ hj : j < 156, CodesAt ⟨j,hj⟩
def codeSuffix00 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := goodCodes
lemma codeSuffix00_subset : codeSuffix00 ⊆ goodCodes := by
  intro x hx
  exact hx
def codeSuffix01 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,2,1,2,2),(1,2,1,2,3),(1,2,1,3,1),(1,2,1,3,2),(1,2,1,3,3),(1,2,2,1,2),(1,2,2,1,3),(1,2,2,3,2),(1,2,3,1,1),(1,2,3,1,2),(1,2,3,1,3),(1,2,3,2,1),(1,2,3,2,2),(1,2,3,2,3),(1,2,3,3,1),(1,2,3,3,2),(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix01_subset : codeSuffix01 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix01 at hx
  apply codeSuffix00_subset
  unfold codeSuffix00 goodCodes
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix02 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,3,1,1,2),(1,3,1,1,3),(1,3,1,2,1),(1,3,1,2,2),(1,3,1,2,3),(1,3,1,3,1),(1,3,1,3,2),(1,3,1,3,3),(1,3,2,1,2),(1,3,2,1,3),(1,3,2,2,2),(1,3,2,2,3),(1,3,2,3,2),(1,3,2,3,3),(1,3,3,1,2),(1,3,3,1,3),(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix02_subset : codeSuffix02 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix02 at hx
  apply codeSuffix01_subset
  unfold codeSuffix01
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix03 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,3,3,2,1),(1,3,3,2,2),(1,3,3,2,3),(1,3,3,3,2),(2,1,1,2,1),(2,1,1,2,3),(2,1,1,3,1),(2,1,2,1,1),(2,1,2,1,2),(2,1,2,1,3),(2,1,2,2,1),(2,1,2,2,2),(2,1,2,2,3),(2,1,2,3,1),(2,1,2,3,2),(2,1,2,3,3),(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix03_subset : codeSuffix03 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix03 at hx
  apply codeSuffix02_subset
  unfold codeSuffix02
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix04 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(2,1,3,1,1),(2,1,3,1,2),(2,1,3,1,3),(2,1,3,2,1),(2,1,3,2,2),(2,1,3,2,3),(2,1,3,3,1),(2,1,3,3,2),(2,2,1,2,1),(2,2,1,3,1),(2,2,1,3,2),(2,2,2,1,2),(2,2,2,3,1),(2,2,2,3,2),(2,2,3,1,1),(2,2,3,1,2),(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix04_subset : codeSuffix04 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix04 at hx
  apply codeSuffix03_subset
  unfold codeSuffix03
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix05 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(2,2,3,2,1),(2,2,3,2,2),(2,2,3,3,1),(2,2,3,3,2),(2,3,1,2,1),(2,3,1,2,2),(2,3,1,2,3),(2,3,1,3,1),(2,3,1,3,2),(2,3,1,3,3),(2,3,2,1,2),(2,3,2,1,3),(2,3,2,2,1),(2,3,2,2,2),(2,3,2,2,3),(2,3,2,3,1),(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix05_subset : codeSuffix05 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix05 at hx
  apply codeSuffix04_subset
  unfold codeSuffix04
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix06 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(2,3,2,3,2),(2,3,2,3,3),(2,3,3,1,2),(2,3,3,2,1),(2,3,3,2,2),(2,3,3,2,3),(2,3,3,3,1),(2,3,3,3,2),(3,1,1,1,1),(3,1,1,1,3),(3,1,1,2,1),(3,1,1,2,3),(3,1,1,3,1),(3,1,1,3,3),(3,1,2,1,1),(3,1,2,1,2),(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix06_subset : codeSuffix06 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix06 at hx
  apply codeSuffix05_subset
  unfold codeSuffix05
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix07 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(3,1,2,1,3),(3,1,2,2,1),(3,1,2,2,3),(3,1,2,3,1),(3,1,2,3,2),(3,1,2,3,3),(3,1,3,1,1),(3,1,3,1,2),(3,1,3,1,3),(3,1,3,2,1),(3,1,3,2,3),(3,1,3,3,1),(3,2,1,1,1),(3,2,1,1,2),(3,2,1,1,3),(3,2,1,2,1),(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix07_subset : codeSuffix07 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix07 at hx
  apply codeSuffix06_subset
  unfold codeSuffix06
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix08 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(3,2,1,2,3),(3,2,1,3,1),(3,2,1,3,2),(3,2,1,3,3),(3,2,2,1,1),(3,2,2,1,2),(3,2,2,1,3),(3,2,2,3,1),(3,2,2,3,2),(3,2,2,3,3),(3,2,3,1,1),(3,2,3,1,2),(3,2,3,1,3),(3,2,3,2,1),(3,2,3,3,1),(3,2,3,3,2),(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix08_subset : codeSuffix08 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix08 at hx
  apply codeSuffix07_subset
  unfold codeSuffix07
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix09 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(3,3,1,1,3),(3,3,1,2,1),(3,3,1,2,3),(3,3,1,3,1),(3,3,1,3,2),(3,3,1,3,3),(3,3,2,1,2),(3,3,2,1,3),(3,3,2,2,3),(3,3,2,3,1),(3,3,2,3,2),(3,3,2,3,3)}
lemma codeSuffix09_subset : codeSuffix09 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix09 at hx
  apply codeSuffix08_subset
  unfold codeSuffix08
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
lemma codes_case0 : CodesAt 0 := by
  have hv : CodesValue 0 = (1,1,1,1,3) := by rfl
  have hm : (1,1,1,1,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case1 : CodesAt 1 := by
  have hv : CodesValue 1 = (1,1,1,2,1) := by rfl
  have hm : (1,1,1,2,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case2 : CodesAt 2 := by
  have hv : CodesValue 2 = (1,1,1,2,3) := by rfl
  have hm : (1,1,1,2,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case3 : CodesAt 3 := by
  have hv : CodesValue 3 = (1,1,2,1,2) := by rfl
  have hm : (1,1,2,1,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case4 : CodesAt 4 := by
  have hv : CodesValue 4 = (1,1,2,1,3) := by rfl
  have hm : (1,1,2,1,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case5 : CodesAt 5 := by
  have hv : CodesValue 5 = (1,1,2,2,3) := by rfl
  have hm : (1,1,2,2,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case6 : CodesAt 6 := by
  have hv : CodesValue 6 = (1,1,3,1,1) := by rfl
  have hm : (1,1,3,1,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case7 : CodesAt 7 := by
  have hv : CodesValue 7 = (1,1,3,1,2) := by rfl
  have hm : (1,1,3,1,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case8 : CodesAt 8 := by
  have hv : CodesValue 8 = (1,1,3,1,3) := by rfl
  have hm : (1,1,3,1,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case9 : CodesAt 9 := by
  have hv : CodesValue 9 = (1,1,3,2,1) := by rfl
  have hm : (1,1,3,2,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case10 : CodesAt 10 := by
  have hv : CodesValue 10 = (1,1,3,2,2) := by rfl
  have hm : (1,1,3,2,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case11 : CodesAt 11 := by
  have hv : CodesValue 11 = (1,1,3,2,3) := by rfl
  have hm : (1,1,3,2,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case12 : CodesAt 12 := by
  have hv : CodesValue 12 = (1,2,1,1,1) := by rfl
  have hm : (1,2,1,1,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case13 : CodesAt 13 := by
  have hv : CodesValue 13 = (1,2,1,1,2) := by rfl
  have hm : (1,2,1,1,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case14 : CodesAt 14 := by
  have hv : CodesValue 14 = (1,2,1,1,3) := by rfl
  have hm : (1,2,1,1,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case15 : CodesAt 15 := by
  have hv : CodesValue 15 = (1,2,1,2,1) := by rfl
  have hm : (1,2,1,2,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case16 : CodesAt 16 := by
  have hv : CodesValue 16 = (1,2,1,2,2) := by rfl
  have hm : (1,2,1,2,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case17 : CodesAt 17 := by
  have hv : CodesValue 17 = (1,2,1,2,3) := by rfl
  have hm : (1,2,1,2,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case18 : CodesAt 18 := by
  have hv : CodesValue 18 = (1,2,1,3,1) := by rfl
  have hm : (1,2,1,3,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case19 : CodesAt 19 := by
  have hv : CodesValue 19 = (1,2,1,3,2) := by rfl
  have hm : (1,2,1,3,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case20 : CodesAt 20 := by
  have hv : CodesValue 20 = (1,2,1,3,3) := by rfl
  have hm : (1,2,1,3,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case21 : CodesAt 21 := by
  have hv : CodesValue 21 = (1,2,2,1,2) := by rfl
  have hm : (1,2,2,1,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case22 : CodesAt 22 := by
  have hv : CodesValue 22 = (1,2,2,1,3) := by rfl
  have hm : (1,2,2,1,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case23 : CodesAt 23 := by
  have hv : CodesValue 23 = (1,2,2,3,2) := by rfl
  have hm : (1,2,2,3,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case24 : CodesAt 24 := by
  have hv : CodesValue 24 = (1,2,3,1,1) := by rfl
  have hm : (1,2,3,1,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case25 : CodesAt 25 := by
  have hv : CodesValue 25 = (1,2,3,1,2) := by rfl
  have hm : (1,2,3,1,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case26 : CodesAt 26 := by
  have hv : CodesValue 26 = (1,2,3,1,3) := by rfl
  have hm : (1,2,3,1,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case27 : CodesAt 27 := by
  have hv : CodesValue 27 = (1,2,3,2,1) := by rfl
  have hm : (1,2,3,2,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case28 : CodesAt 28 := by
  have hv : CodesValue 28 = (1,2,3,2,2) := by rfl
  have hm : (1,2,3,2,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case29 : CodesAt 29 := by
  have hv : CodesValue 29 = (1,2,3,2,3) := by rfl
  have hm : (1,2,3,2,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case30 : CodesAt 30 := by
  have hv : CodesValue 30 = (1,2,3,3,1) := by rfl
  have hm : (1,2,3,3,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case31 : CodesAt 31 := by
  have hv : CodesValue 31 = (1,2,3,3,2) := by rfl
  have hm : (1,2,3,3,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case32 : CodesAt 32 := by
  have hv : CodesValue 32 = (1,3,1,1,2) := by rfl
  have hm : (1,3,1,1,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case33 : CodesAt 33 := by
  have hv : CodesValue 33 = (1,3,1,1,3) := by rfl
  have hm : (1,3,1,1,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case34 : CodesAt 34 := by
  have hv : CodesValue 34 = (1,3,1,2,1) := by rfl
  have hm : (1,3,1,2,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case35 : CodesAt 35 := by
  have hv : CodesValue 35 = (1,3,1,2,2) := by rfl
  have hm : (1,3,1,2,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case36 : CodesAt 36 := by
  have hv : CodesValue 36 = (1,3,1,2,3) := by rfl
  have hm : (1,3,1,2,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case37 : CodesAt 37 := by
  have hv : CodesValue 37 = (1,3,1,3,1) := by rfl
  have hm : (1,3,1,3,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case38 : CodesAt 38 := by
  have hv : CodesValue 38 = (1,3,1,3,2) := by rfl
  have hm : (1,3,1,3,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case39 : CodesAt 39 := by
  have hv : CodesValue 39 = (1,3,1,3,3) := by rfl
  have hm : (1,3,1,3,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case40 : CodesAt 40 := by
  have hv : CodesValue 40 = (1,3,2,1,2) := by rfl
  have hm : (1,3,2,1,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case41 : CodesAt 41 := by
  have hv : CodesValue 41 = (1,3,2,1,3) := by rfl
  have hm : (1,3,2,1,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case42 : CodesAt 42 := by
  have hv : CodesValue 42 = (1,3,2,2,2) := by rfl
  have hm : (1,3,2,2,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case43 : CodesAt 43 := by
  have hv : CodesValue 43 = (1,3,2,2,3) := by rfl
  have hm : (1,3,2,2,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case44 : CodesAt 44 := by
  have hv : CodesValue 44 = (1,3,2,3,2) := by rfl
  have hm : (1,3,2,3,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case45 : CodesAt 45 := by
  have hv : CodesValue 45 = (1,3,2,3,3) := by rfl
  have hm : (1,3,2,3,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case46 : CodesAt 46 := by
  have hv : CodesValue 46 = (1,3,3,1,2) := by rfl
  have hm : (1,3,3,1,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case47 : CodesAt 47 := by
  have hv : CodesValue 47 = (1,3,3,1,3) := by rfl
  have hm : (1,3,3,1,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case48 : CodesAt 48 := by
  have hv : CodesValue 48 = (1,3,3,2,1) := by rfl
  have hm : (1,3,3,2,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case49 : CodesAt 49 := by
  have hv : CodesValue 49 = (1,3,3,2,2) := by rfl
  have hm : (1,3,3,2,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case50 : CodesAt 50 := by
  have hv : CodesValue 50 = (1,3,3,2,3) := by rfl
  have hm : (1,3,3,2,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case51 : CodesAt 51 := by
  have hv : CodesValue 51 = (1,3,3,3,2) := by rfl
  have hm : (1,3,3,3,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case52 : CodesAt 52 := by
  have hv : CodesValue 52 = (2,1,1,2,1) := by rfl
  have hm : (2,1,1,2,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case53 : CodesAt 53 := by
  have hv : CodesValue 53 = (2,1,1,2,3) := by rfl
  have hm : (2,1,1,2,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case54 : CodesAt 54 := by
  have hv : CodesValue 54 = (2,1,1,3,1) := by rfl
  have hm : (2,1,1,3,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case55 : CodesAt 55 := by
  have hv : CodesValue 55 = (2,1,2,1,1) := by rfl
  have hm : (2,1,2,1,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case56 : CodesAt 56 := by
  have hv : CodesValue 56 = (2,1,2,1,2) := by rfl
  have hm : (2,1,2,1,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case57 : CodesAt 57 := by
  have hv : CodesValue 57 = (2,1,2,1,3) := by rfl
  have hm : (2,1,2,1,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case58 : CodesAt 58 := by
  have hv : CodesValue 58 = (2,1,2,2,1) := by rfl
  have hm : (2,1,2,2,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case59 : CodesAt 59 := by
  have hv : CodesValue 59 = (2,1,2,2,2) := by rfl
  have hm : (2,1,2,2,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case60 : CodesAt 60 := by
  have hv : CodesValue 60 = (2,1,2,2,3) := by rfl
  have hm : (2,1,2,2,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case61 : CodesAt 61 := by
  have hv : CodesValue 61 = (2,1,2,3,1) := by rfl
  have hm : (2,1,2,3,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case62 : CodesAt 62 := by
  have hv : CodesValue 62 = (2,1,2,3,2) := by rfl
  have hm : (2,1,2,3,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case63 : CodesAt 63 := by
  have hv : CodesValue 63 = (2,1,2,3,3) := by rfl
  have hm : (2,1,2,3,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case64 : CodesAt 64 := by
  have hv : CodesValue 64 = (2,1,3,1,1) := by rfl
  have hm : (2,1,3,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case65 : CodesAt 65 := by
  have hv : CodesValue 65 = (2,1,3,1,2) := by rfl
  have hm : (2,1,3,1,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case66 : CodesAt 66 := by
  have hv : CodesValue 66 = (2,1,3,1,3) := by rfl
  have hm : (2,1,3,1,3) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case67 : CodesAt 67 := by
  have hv : CodesValue 67 = (2,1,3,2,1) := by rfl
  have hm : (2,1,3,2,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case68 : CodesAt 68 := by
  have hv : CodesValue 68 = (2,1,3,2,2) := by rfl
  have hm : (2,1,3,2,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case69 : CodesAt 69 := by
  have hv : CodesValue 69 = (2,1,3,2,3) := by rfl
  have hm : (2,1,3,2,3) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case70 : CodesAt 70 := by
  have hv : CodesValue 70 = (2,1,3,3,1) := by rfl
  have hm : (2,1,3,3,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case71 : CodesAt 71 := by
  have hv : CodesValue 71 = (2,1,3,3,2) := by rfl
  have hm : (2,1,3,3,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case72 : CodesAt 72 := by
  have hv : CodesValue 72 = (2,2,1,2,1) := by rfl
  have hm : (2,2,1,2,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case73 : CodesAt 73 := by
  have hv : CodesValue 73 = (2,2,1,3,1) := by rfl
  have hm : (2,2,1,3,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case74 : CodesAt 74 := by
  have hv : CodesValue 74 = (2,2,1,3,2) := by rfl
  have hm : (2,2,1,3,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case75 : CodesAt 75 := by
  have hv : CodesValue 75 = (2,2,2,1,2) := by rfl
  have hm : (2,2,2,1,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case76 : CodesAt 76 := by
  have hv : CodesValue 76 = (2,2,2,3,1) := by rfl
  have hm : (2,2,2,3,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case77 : CodesAt 77 := by
  have hv : CodesValue 77 = (2,2,2,3,2) := by rfl
  have hm : (2,2,2,3,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case78 : CodesAt 78 := by
  have hv : CodesValue 78 = (2,2,3,1,1) := by rfl
  have hm : (2,2,3,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case79 : CodesAt 79 := by
  have hv : CodesValue 79 = (2,2,3,1,2) := by rfl
  have hm : (2,2,3,1,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case80 : CodesAt 80 := by
  have hv : CodesValue 80 = (2,2,3,2,1) := by rfl
  have hm : (2,2,3,2,1) ∈ codeSuffix05 := by
    unfold codeSuffix05
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case81 : CodesAt 81 := by
  have hv : CodesValue 81 = (2,2,3,2,2) := by rfl
  have hm : (2,2,3,2,2) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case82 : CodesAt 82 := by
  have hv : CodesValue 82 = (2,2,3,3,1) := by rfl
  have hm : (2,2,3,3,1) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case83 : CodesAt 83 := by
  have hv : CodesValue 83 = (2,2,3,3,2) := by rfl
  have hm : (2,2,3,3,2) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case84 : CodesAt 84 := by
  have hv : CodesValue 84 = (2,3,1,2,1) := by rfl
  have hm : (2,3,1,2,1) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case85 : CodesAt 85 := by
  have hv : CodesValue 85 = (2,3,1,2,2) := by rfl
  have hm : (2,3,1,2,2) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case86 : CodesAt 86 := by
  have hv : CodesValue 86 = (2,3,1,2,3) := by rfl
  have hm : (2,3,1,2,3) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case87 : CodesAt 87 := by
  have hv : CodesValue 87 = (2,3,1,3,1) := by rfl
  have hm : (2,3,1,3,1) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case88 : CodesAt 88 := by
  have hv : CodesValue 88 = (2,3,1,3,2) := by rfl
  have hm : (2,3,1,3,2) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case89 : CodesAt 89 := by
  have hv : CodesValue 89 = (2,3,1,3,3) := by rfl
  have hm : (2,3,1,3,3) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case90 : CodesAt 90 := by
  have hv : CodesValue 90 = (2,3,2,1,2) := by rfl
  have hm : (2,3,2,1,2) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case91 : CodesAt 91 := by
  have hv : CodesValue 91 = (2,3,2,1,3) := by rfl
  have hm : (2,3,2,1,3) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case92 : CodesAt 92 := by
  have hv : CodesValue 92 = (2,3,2,2,1) := by rfl
  have hm : (2,3,2,2,1) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case93 : CodesAt 93 := by
  have hv : CodesValue 93 = (2,3,2,2,2) := by rfl
  have hm : (2,3,2,2,2) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case94 : CodesAt 94 := by
  have hv : CodesValue 94 = (2,3,2,2,3) := by rfl
  have hm : (2,3,2,2,3) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case95 : CodesAt 95 := by
  have hv : CodesValue 95 = (2,3,2,3,1) := by rfl
  have hm : (2,3,2,3,1) ∈ codeSuffix05 := by
    unfold codeSuffix05
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix05_subset hm)
lemma codes_case96 : CodesAt 96 := by
  have hv : CodesValue 96 = (2,3,2,3,2) := by rfl
  have hm : (2,3,2,3,2) ∈ codeSuffix06 := by
    unfold codeSuffix06
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case97 : CodesAt 97 := by
  have hv : CodesValue 97 = (2,3,2,3,3) := by rfl
  have hm : (2,3,2,3,3) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case98 : CodesAt 98 := by
  have hv : CodesValue 98 = (2,3,3,1,2) := by rfl
  have hm : (2,3,3,1,2) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case99 : CodesAt 99 := by
  have hv : CodesValue 99 = (2,3,3,2,1) := by rfl
  have hm : (2,3,3,2,1) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case100 : CodesAt 100 := by
  have hv : CodesValue 100 = (2,3,3,2,2) := by rfl
  have hm : (2,3,3,2,2) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case101 : CodesAt 101 := by
  have hv : CodesValue 101 = (2,3,3,2,3) := by rfl
  have hm : (2,3,3,2,3) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case102 : CodesAt 102 := by
  have hv : CodesValue 102 = (2,3,3,3,1) := by rfl
  have hm : (2,3,3,3,1) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case103 : CodesAt 103 := by
  have hv : CodesValue 103 = (2,3,3,3,2) := by rfl
  have hm : (2,3,3,3,2) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case104 : CodesAt 104 := by
  have hv : CodesValue 104 = (3,1,1,1,1) := by rfl
  have hm : (3,1,1,1,1) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case105 : CodesAt 105 := by
  have hv : CodesValue 105 = (3,1,1,1,3) := by rfl
  have hm : (3,1,1,1,3) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case106 : CodesAt 106 := by
  have hv : CodesValue 106 = (3,1,1,2,1) := by rfl
  have hm : (3,1,1,2,1) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case107 : CodesAt 107 := by
  have hv : CodesValue 107 = (3,1,1,2,3) := by rfl
  have hm : (3,1,1,2,3) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case108 : CodesAt 108 := by
  have hv : CodesValue 108 = (3,1,1,3,1) := by rfl
  have hm : (3,1,1,3,1) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case109 : CodesAt 109 := by
  have hv : CodesValue 109 = (3,1,1,3,3) := by rfl
  have hm : (3,1,1,3,3) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case110 : CodesAt 110 := by
  have hv : CodesValue 110 = (3,1,2,1,1) := by rfl
  have hm : (3,1,2,1,1) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case111 : CodesAt 111 := by
  have hv : CodesValue 111 = (3,1,2,1,2) := by rfl
  have hm : (3,1,2,1,2) ∈ codeSuffix06 := by
    unfold codeSuffix06
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix06_subset hm)
lemma codes_case112 : CodesAt 112 := by
  have hv : CodesValue 112 = (3,1,2,1,3) := by rfl
  have hm : (3,1,2,1,3) ∈ codeSuffix07 := by
    unfold codeSuffix07
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case113 : CodesAt 113 := by
  have hv : CodesValue 113 = (3,1,2,2,1) := by rfl
  have hm : (3,1,2,2,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case114 : CodesAt 114 := by
  have hv : CodesValue 114 = (3,1,2,2,3) := by rfl
  have hm : (3,1,2,2,3) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case115 : CodesAt 115 := by
  have hv : CodesValue 115 = (3,1,2,3,1) := by rfl
  have hm : (3,1,2,3,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case116 : CodesAt 116 := by
  have hv : CodesValue 116 = (3,1,2,3,2) := by rfl
  have hm : (3,1,2,3,2) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case117 : CodesAt 117 := by
  have hv : CodesValue 117 = (3,1,2,3,3) := by rfl
  have hm : (3,1,2,3,3) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case118 : CodesAt 118 := by
  have hv : CodesValue 118 = (3,1,3,1,1) := by rfl
  have hm : (3,1,3,1,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case119 : CodesAt 119 := by
  have hv : CodesValue 119 = (3,1,3,1,2) := by rfl
  have hm : (3,1,3,1,2) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case120 : CodesAt 120 := by
  have hv : CodesValue 120 = (3,1,3,1,3) := by rfl
  have hm : (3,1,3,1,3) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case121 : CodesAt 121 := by
  have hv : CodesValue 121 = (3,1,3,2,1) := by rfl
  have hm : (3,1,3,2,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case122 : CodesAt 122 := by
  have hv : CodesValue 122 = (3,1,3,2,3) := by rfl
  have hm : (3,1,3,2,3) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case123 : CodesAt 123 := by
  have hv : CodesValue 123 = (3,1,3,3,1) := by rfl
  have hm : (3,1,3,3,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case124 : CodesAt 124 := by
  have hv : CodesValue 124 = (3,2,1,1,1) := by rfl
  have hm : (3,2,1,1,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case125 : CodesAt 125 := by
  have hv : CodesValue 125 = (3,2,1,1,2) := by rfl
  have hm : (3,2,1,1,2) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case126 : CodesAt 126 := by
  have hv : CodesValue 126 = (3,2,1,1,3) := by rfl
  have hm : (3,2,1,1,3) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case127 : CodesAt 127 := by
  have hv : CodesValue 127 = (3,2,1,2,1) := by rfl
  have hm : (3,2,1,2,1) ∈ codeSuffix07 := by
    unfold codeSuffix07
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix07_subset hm)
lemma codes_case128 : CodesAt 128 := by
  have hv : CodesValue 128 = (3,2,1,2,3) := by rfl
  have hm : (3,2,1,2,3) ∈ codeSuffix08 := by
    unfold codeSuffix08
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case129 : CodesAt 129 := by
  have hv : CodesValue 129 = (3,2,1,3,1) := by rfl
  have hm : (3,2,1,3,1) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case130 : CodesAt 130 := by
  have hv : CodesValue 130 = (3,2,1,3,2) := by rfl
  have hm : (3,2,1,3,2) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case131 : CodesAt 131 := by
  have hv : CodesValue 131 = (3,2,1,3,3) := by rfl
  have hm : (3,2,1,3,3) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case132 : CodesAt 132 := by
  have hv : CodesValue 132 = (3,2,2,1,1) := by rfl
  have hm : (3,2,2,1,1) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case133 : CodesAt 133 := by
  have hv : CodesValue 133 = (3,2,2,1,2) := by rfl
  have hm : (3,2,2,1,2) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case134 : CodesAt 134 := by
  have hv : CodesValue 134 = (3,2,2,1,3) := by rfl
  have hm : (3,2,2,1,3) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case135 : CodesAt 135 := by
  have hv : CodesValue 135 = (3,2,2,3,1) := by rfl
  have hm : (3,2,2,3,1) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case136 : CodesAt 136 := by
  have hv : CodesValue 136 = (3,2,2,3,2) := by rfl
  have hm : (3,2,2,3,2) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case137 : CodesAt 137 := by
  have hv : CodesValue 137 = (3,2,2,3,3) := by rfl
  have hm : (3,2,2,3,3) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case138 : CodesAt 138 := by
  have hv : CodesValue 138 = (3,2,3,1,1) := by rfl
  have hm : (3,2,3,1,1) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case139 : CodesAt 139 := by
  have hv : CodesValue 139 = (3,2,3,1,2) := by rfl
  have hm : (3,2,3,1,2) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case140 : CodesAt 140 := by
  have hv : CodesValue 140 = (3,2,3,1,3) := by rfl
  have hm : (3,2,3,1,3) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case141 : CodesAt 141 := by
  have hv : CodesValue 141 = (3,2,3,2,1) := by rfl
  have hm : (3,2,3,2,1) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case142 : CodesAt 142 := by
  have hv : CodesValue 142 = (3,2,3,3,1) := by rfl
  have hm : (3,2,3,3,1) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case143 : CodesAt 143 := by
  have hv : CodesValue 143 = (3,2,3,3,2) := by rfl
  have hm : (3,2,3,3,2) ∈ codeSuffix08 := by
    unfold codeSuffix08
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix08_subset hm)
lemma codes_case144 : CodesAt 144 := by
  have hv : CodesValue 144 = (3,3,1,1,3) := by rfl
  have hm : (3,3,1,1,3) ∈ codeSuffix09 := by
    unfold codeSuffix09
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case145 : CodesAt 145 := by
  have hv : CodesValue 145 = (3,3,1,2,1) := by rfl
  have hm : (3,3,1,2,1) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case146 : CodesAt 146 := by
  have hv : CodesValue 146 = (3,3,1,2,3) := by rfl
  have hm : (3,3,1,2,3) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case147 : CodesAt 147 := by
  have hv : CodesValue 147 = (3,3,1,3,1) := by rfl
  have hm : (3,3,1,3,1) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case148 : CodesAt 148 := by
  have hv : CodesValue 148 = (3,3,1,3,2) := by rfl
  have hm : (3,3,1,3,2) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case149 : CodesAt 149 := by
  have hv : CodesValue 149 = (3,3,1,3,3) := by rfl
  have hm : (3,3,1,3,3) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case150 : CodesAt 150 := by
  have hv : CodesValue 150 = (3,3,2,1,2) := by rfl
  have hm : (3,3,2,1,2) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case151 : CodesAt 151 := by
  have hv : CodesValue 151 = (3,3,2,1,3) := by rfl
  have hm : (3,3,2,1,3) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case152 : CodesAt 152 := by
  have hv : CodesValue 152 = (3,3,2,2,3) := by rfl
  have hm : (3,3,2,2,3) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case153 : CodesAt 153 := by
  have hv : CodesValue 153 = (3,3,2,3,1) := by rfl
  have hm : (3,3,2,3,1) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case154 : CodesAt 154 := by
  have hv : CodesValue 154 = (3,3,2,3,2) := by rfl
  have hm : (3,3,2,3,2) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_case155 : CodesAt 155 := by
  have hv : CodesValue 155 = (3,3,2,3,3) := by rfl
  have hm : (3,3,2,3,3) ∈ codeSuffix09 := by
    unfold codeSuffix09
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_singleton_self _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix09_subset hm)
lemma codes_interval00 : FiniteIntervals.Covers CodesIndex 0 16 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 0 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case0
  · intro hj
    exact codes_case1
  · intro hj
    exact codes_case2
  · intro hj
    exact codes_case3
  · intro hj
    exact codes_case4
  · intro hj
    exact codes_case5
  · intro hj
    exact codes_case6
  · intro hj
    exact codes_case7
  · intro hj
    exact codes_case8
  · intro hj
    exact codes_case9
  · intro hj
    exact codes_case10
  · intro hj
    exact codes_case11
  · intro hj
    exact codes_case12
  · intro hj
    exact codes_case13
  · intro hj
    exact codes_case14
  · intro hj
    exact codes_case15
lemma codes_interval01 : FiniteIntervals.Covers CodesIndex 16 32 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 16 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case16
  · intro hj
    exact codes_case17
  · intro hj
    exact codes_case18
  · intro hj
    exact codes_case19
  · intro hj
    exact codes_case20
  · intro hj
    exact codes_case21
  · intro hj
    exact codes_case22
  · intro hj
    exact codes_case23
  · intro hj
    exact codes_case24
  · intro hj
    exact codes_case25
  · intro hj
    exact codes_case26
  · intro hj
    exact codes_case27
  · intro hj
    exact codes_case28
  · intro hj
    exact codes_case29
  · intro hj
    exact codes_case30
  · intro hj
    exact codes_case31
lemma codes_interval02 : FiniteIntervals.Covers CodesIndex 32 48 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 32 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case32
  · intro hj
    exact codes_case33
  · intro hj
    exact codes_case34
  · intro hj
    exact codes_case35
  · intro hj
    exact codes_case36
  · intro hj
    exact codes_case37
  · intro hj
    exact codes_case38
  · intro hj
    exact codes_case39
  · intro hj
    exact codes_case40
  · intro hj
    exact codes_case41
  · intro hj
    exact codes_case42
  · intro hj
    exact codes_case43
  · intro hj
    exact codes_case44
  · intro hj
    exact codes_case45
  · intro hj
    exact codes_case46
  · intro hj
    exact codes_case47
lemma codes_interval03 : FiniteIntervals.Covers CodesIndex 48 64 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 48 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case48
  · intro hj
    exact codes_case49
  · intro hj
    exact codes_case50
  · intro hj
    exact codes_case51
  · intro hj
    exact codes_case52
  · intro hj
    exact codes_case53
  · intro hj
    exact codes_case54
  · intro hj
    exact codes_case55
  · intro hj
    exact codes_case56
  · intro hj
    exact codes_case57
  · intro hj
    exact codes_case58
  · intro hj
    exact codes_case59
  · intro hj
    exact codes_case60
  · intro hj
    exact codes_case61
  · intro hj
    exact codes_case62
  · intro hj
    exact codes_case63
lemma codes_interval04 : FiniteIntervals.Covers CodesIndex 64 80 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 64 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case64
  · intro hj
    exact codes_case65
  · intro hj
    exact codes_case66
  · intro hj
    exact codes_case67
  · intro hj
    exact codes_case68
  · intro hj
    exact codes_case69
  · intro hj
    exact codes_case70
  · intro hj
    exact codes_case71
  · intro hj
    exact codes_case72
  · intro hj
    exact codes_case73
  · intro hj
    exact codes_case74
  · intro hj
    exact codes_case75
  · intro hj
    exact codes_case76
  · intro hj
    exact codes_case77
  · intro hj
    exact codes_case78
  · intro hj
    exact codes_case79
lemma codes_interval05 : FiniteIntervals.Covers CodesIndex 80 96 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 80 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case80
  · intro hj
    exact codes_case81
  · intro hj
    exact codes_case82
  · intro hj
    exact codes_case83
  · intro hj
    exact codes_case84
  · intro hj
    exact codes_case85
  · intro hj
    exact codes_case86
  · intro hj
    exact codes_case87
  · intro hj
    exact codes_case88
  · intro hj
    exact codes_case89
  · intro hj
    exact codes_case90
  · intro hj
    exact codes_case91
  · intro hj
    exact codes_case92
  · intro hj
    exact codes_case93
  · intro hj
    exact codes_case94
  · intro hj
    exact codes_case95
lemma codes_interval06 : FiniteIntervals.Covers CodesIndex 96 112 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 96 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case96
  · intro hj
    exact codes_case97
  · intro hj
    exact codes_case98
  · intro hj
    exact codes_case99
  · intro hj
    exact codes_case100
  · intro hj
    exact codes_case101
  · intro hj
    exact codes_case102
  · intro hj
    exact codes_case103
  · intro hj
    exact codes_case104
  · intro hj
    exact codes_case105
  · intro hj
    exact codes_case106
  · intro hj
    exact codes_case107
  · intro hj
    exact codes_case108
  · intro hj
    exact codes_case109
  · intro hj
    exact codes_case110
  · intro hj
    exact codes_case111
lemma codes_interval07 : FiniteIntervals.Covers CodesIndex 112 128 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 112 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case112
  · intro hj
    exact codes_case113
  · intro hj
    exact codes_case114
  · intro hj
    exact codes_case115
  · intro hj
    exact codes_case116
  · intro hj
    exact codes_case117
  · intro hj
    exact codes_case118
  · intro hj
    exact codes_case119
  · intro hj
    exact codes_case120
  · intro hj
    exact codes_case121
  · intro hj
    exact codes_case122
  · intro hj
    exact codes_case123
  · intro hj
    exact codes_case124
  · intro hj
    exact codes_case125
  · intro hj
    exact codes_case126
  · intro hj
    exact codes_case127
lemma codes_interval08 : FiniteIntervals.Covers CodesIndex 128 144 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 128 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case128
  · intro hj
    exact codes_case129
  · intro hj
    exact codes_case130
  · intro hj
    exact codes_case131
  · intro hj
    exact codes_case132
  · intro hj
    exact codes_case133
  · intro hj
    exact codes_case134
  · intro hj
    exact codes_case135
  · intro hj
    exact codes_case136
  · intro hj
    exact codes_case137
  · intro hj
    exact codes_case138
  · intro hj
    exact codes_case139
  · intro hj
    exact codes_case140
  · intro hj
    exact codes_case141
  · intro hj
    exact codes_case142
  · intro hj
    exact codes_case143
lemma codes_interval09 : FiniteIntervals.Covers CodesIndex 144 156 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 144 12
  intro i
  fin_cases i
  · intro hj
    exact codes_case144
  · intro hj
    exact codes_case145
  · intro hj
    exact codes_case146
  · intro hj
    exact codes_case147
  · intro hj
    exact codes_case148
  · intro hj
    exact codes_case149
  · intro hj
    exact codes_case150
  · intro hj
    exact codes_case151
  · intro hj
    exact codes_case152
  · intro hj
    exact codes_case153
  · intro hj
    exact codes_case154
  · intro hj
    exact codes_case155
lemma codes_valid : ∀ i : FiveWordOrbits0.Cases, ((FiveRows0.digit0 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit1 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit2 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit3 (FiveWordOrbits0.caseKey i).val).val + 1,(FiveRows0.digit4 (FiveWordOrbits0.caseKey i).val).val + 1) ∈ goodCodes := by
  intro i
  have hc : FiniteIntervals.Covers CodesIndex 0 156 := (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge codes_interval00 codes_interval01) (FiniteIntervals.merge codes_interval02 (FiniteIntervals.merge codes_interval03 codes_interval04))) (FiniteIntervals.merge (FiniteIntervals.merge codes_interval05 codes_interval06) (FiniteIntervals.merge codes_interval07 (FiniteIntervals.merge codes_interval08 codes_interval09))))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma codes_of_good (j : Fin 243) (hj : j ∈ FiveRows0.good) :
    ((FiveRows0.digit0 j.val).val + 1,(FiveRows0.digit1 j.val).val + 1,(FiveRows0.digit2 j.val).val + 1,(FiveRows0.digit3 j.val).val + 1,(FiveRows0.digit4 j.val).val + 1) ∈ goodCodes := by
  rw [FiveWordOrbits0.good_eq] at hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact codes_valid i

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5)) := by
  have hs := SixProjection40.localBounds o h
  have hc := codes_of_good ⟨FiveRows0.key (smallOrders o),FiveRows0.key_lt (smallOrders o)⟩
    (SixProjection40.catalogue o h)
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
end Erdos184Work.SixProjectionCode40
