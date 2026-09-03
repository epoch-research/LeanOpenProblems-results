import Submission.FiniteIntervals
import Submission.SixProjection31
import Submission.SixRows3
import Submission.FiveWordOrbits3

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.SixProjectionCode31
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection31
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
lemma row0_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows3.words0 (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc0 (SixRows3.key2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row0_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows3.words0 (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc0 (SixRows3.key2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row0_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows3.words0 (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows3.key2 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows3.words0 (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows3.key2 (q,(Sum.inl (Sum.inr ())))) = (FiveRows3.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inr ())))).vertex =
      FiveRows3.words0 (FiveRows3.key0 (smallOrder0 (q,(Sum.inr ())))) →
    enc0 (SixRows3.key2 (q,(Sum.inr ()))) = (FiveRows3.key0 (smallOrder0 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 q)).vertex =
      FiveRows3.words0 (FiveRows3.key0 (smallOrder0 q)) →
    enc0 (SixRows3.key2 q) = (FiveRows3.key0 (smallOrder0 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0 q
  · exact row0_1 q
  · exact row0_2 q
  · exact row0_3 q
  · exact row0_4 q

def enc1 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
lemma row1_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows3.words1 (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc1 (SixRows3.key3 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows3.words1 (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc1 (SixRows3.key3 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows3.words1 (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc1 (SixRows3.key3 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row1_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows3.words1 (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))) →
    enc1 (SixRows3.key3 (q,(Sum.inl (Sum.inr ())))) = (FiveRows3.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row1_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inr ())))).vertex =
      FiveRows3.words1 (FiveRows3.key1 (smallOrder1 (q,(Sum.inr ())))) →
    enc1 (SixRows3.key3 (q,(Sum.inr ()))) = (FiveRows3.key1 (smallOrder1 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row1 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder1 q)).vertex =
      FiveRows3.words1 (FiveRows3.key1 (smallOrder1 q)) →
    enc1 (SixRows3.key3 q) = (FiveRows3.key1 (smallOrder1 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row1_0 q
  · exact row1_1 q
  · exact row1_2 q
  · exact row1_3 q
  · exact row1_4 q

def enc2 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
lemma row2_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows3.words2 (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc2 (SixRows3.key4 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row2_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows3.words2 (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc2 (SixRows3.key4 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row2_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows3.words2 (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc2 (SixRows3.key4 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row2_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows3.words2 (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inr ()))))) →
    enc2 (SixRows3.key4 (q,(Sum.inl (Sum.inr ())))) = (FiveRows3.key2 (smallOrder2 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row2_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inr ())))).vertex =
      FiveRows3.words2 (FiveRows3.key2 (smallOrder2 (q,(Sum.inr ())))) →
    enc2 (SixRows3.key4 (q,(Sum.inr ()))) = (FiveRows3.key2 (smallOrder2 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row2 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder2 q)).vertex =
      FiveRows3.words2 (FiveRows3.key2 (smallOrder2 q)) →
    enc2 (SixRows3.key4 q) = (FiveRows3.key2 (smallOrder2 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row2_0 q
  · exact row2_1 q
  · exact row2_2 q
  · exact row2_3 q
  · exact row2_4 q

def enc3 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
lemma row3_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows3.words3 (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc3 (SixRows3.key5 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row3_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows3.words3 (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc3 (SixRows3.key5 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row3_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows3.words3 (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc3 (SixRows3.key5 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row3_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder3 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows3.words3 (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inr ()))))) →
    enc3 (SixRows3.key5 (q,(Sum.inl (Sum.inr ())))) = (FiveRows3.key3 (smallOrder3 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row3_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder3 (q,(Sum.inr ())))).vertex =
      FiveRows3.words3 (FiveRows3.key3 (smallOrder3 (q,(Sum.inr ())))) →
    enc3 (SixRows3.key5 (q,(Sum.inr ()))) = (FiveRows3.key3 (smallOrder3 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row3 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder3 q)).vertex =
      FiveRows3.words3 (FiveRows3.key3 (smallOrder3 q)) →
    enc3 (SixRows3.key5 q) = (FiveRows3.key3 (smallOrder3 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row3_0 q
  · exact row3_1 q
  · exact row3_2 q
  · exact row3_3 q
  · exact row3_4 q

def enc4 : Fin 60 → ℕ := ![1,2,3,2,3,1,2,1,3,1,3,2,2,3,1,3,1,2,1,3,2,3,2,1,1,2,3,2,3,1,1,2,1,2,3,2,3,2,3,1,3,1,2,1,3,3,2,1,2,1,3,3,3,3,2,1,2,2,1,1]
lemma row4_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows3.words4 (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc4 (SixRows3.key0 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row4_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows3.words4 (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc4 (SixRows3.key0 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row4_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows3.words4 (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc4 (SixRows3.key0 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row4_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows3.words4 (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inr ()))))) →
    enc4 (SixRows3.key0 (q,(Sum.inl (Sum.inr ())))) = (FiveRows3.key4 (smallOrder4 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row4_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 (q,(Sum.inr ())))).vertex =
      FiveRows3.words4 (FiveRows3.key4 (smallOrder4 (q,(Sum.inr ())))) →
    enc4 (SixRows3.key0 (q,(Sum.inr ()))) = (FiveRows3.key4 (smallOrder4 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row4 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows3.words4 (FiveRows3.key4 (smallOrder4 q)) →
    enc4 (SixRows3.key0 q) = (FiveRows3.key4 (smallOrder4 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row4_0 q
  · exact row4_1 q
  · exact row4_2 q
  · exact row4_3 q
  · exact row4_4 q

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def Compatible (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop :=
  (enc0 q2,enc1 q3,enc2 q4,enc3 q5,enc4 q0) ∈ goodCodes
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Compatible q0 q1 q2 q3 q4 q5) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

/- Direct catalogue insertion proofs avoid evaluating nested finset deduplication. -/
/- Factored catalogue insertion proofs avoid repeated long prefixes. -/
/- Opaque-index catalogue assembly; value equalities are checked separately. -/
def CodesValue (i : FiveWordOrbits3.Cases) : (ℕ × ℕ × ℕ × ℕ × ℕ) := ((FiveRows3.digit0 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit1 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit2 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit3 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit4 (FiveWordOrbits3.caseKey i).val).val + 1)
def CodesAt (i : FiveWordOrbits3.Cases) : Prop := CodesValue i ∈ goodCodes
def CodesIndex (j : ℕ) : Prop := ∀ hj : j < 24, CodesAt ⟨j,hj⟩
def codeSuffix00 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := goodCodes
lemma codeSuffix00_subset : codeSuffix00 ⊆ goodCodes := by
  intro x hx
  exact hx
def codeSuffix01 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
lemma codeSuffix01_subset : codeSuffix01 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix01 at hx
  apply codeSuffix00_subset
  unfold codeSuffix00 goodCodes
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
lemma codes_case0 : CodesAt 0 := by
  have hv : CodesValue 0 = (7,10,7,10,1) := by rfl
  have hm : (7,10,7,10,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case1 : CodesAt 1 := by
  have hv : CodesValue 1 = (7,10,7,10,2) := by rfl
  have hm : (7,10,7,10,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case2 : CodesAt 2 := by
  have hv : CodesValue 2 = (7,10,7,10,3) := by rfl
  have hm : (7,10,7,10,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case3 : CodesAt 3 := by
  have hv : CodesValue 3 = (7,10,11,8,1) := by rfl
  have hm : (7,10,11,8,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case4 : CodesAt 4 := by
  have hv : CodesValue 4 = (7,10,11,8,2) := by rfl
  have hm : (7,10,11,8,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case5 : CodesAt 5 := by
  have hv : CodesValue 5 = (7,10,11,8,3) := by rfl
  have hm : (7,10,11,8,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case6 : CodesAt 6 := by
  have hv : CodesValue 6 = (8,11,7,10,1) := by rfl
  have hm : (8,11,7,10,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case7 : CodesAt 7 := by
  have hv : CodesValue 7 = (8,11,7,10,2) := by rfl
  have hm : (8,11,7,10,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case8 : CodesAt 8 := by
  have hv : CodesValue 8 = (8,11,7,10,3) := by rfl
  have hm : (8,11,7,10,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case9 : CodesAt 9 := by
  have hv : CodesValue 9 = (8,11,11,8,1) := by rfl
  have hm : (8,11,11,8,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case10 : CodesAt 10 := by
  have hv : CodesValue 10 = (8,11,11,8,2) := by rfl
  have hm : (8,11,11,8,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case11 : CodesAt 11 := by
  have hv : CodesValue 11 = (8,11,11,8,3) := by rfl
  have hm : (8,11,11,8,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case12 : CodesAt 12 := by
  have hv : CodesValue 12 = (10,7,8,11,1) := by rfl
  have hm : (10,7,8,11,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case13 : CodesAt 13 := by
  have hv : CodesValue 13 = (10,7,8,11,2) := by rfl
  have hm : (10,7,8,11,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case14 : CodesAt 14 := by
  have hv : CodesValue 14 = (10,7,8,11,3) := by rfl
  have hm : (10,7,8,11,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case15 : CodesAt 15 := by
  have hv : CodesValue 15 = (10,7,10,7,1) := by rfl
  have hm : (10,7,10,7,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case16 : CodesAt 16 := by
  have hv : CodesValue 16 = (10,7,10,7,2) := by rfl
  have hm : (10,7,10,7,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case17 : CodesAt 17 := by
  have hv : CodesValue 17 = (10,7,10,7,3) := by rfl
  have hm : (10,7,10,7,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case18 : CodesAt 18 := by
  have hv : CodesValue 18 = (11,8,8,11,1) := by rfl
  have hm : (11,8,8,11,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case19 : CodesAt 19 := by
  have hv : CodesValue 19 = (11,8,8,11,2) := by rfl
  have hm : (11,8,8,11,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case20 : CodesAt 20 := by
  have hv : CodesValue 20 = (11,8,8,11,3) := by rfl
  have hm : (11,8,8,11,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case21 : CodesAt 21 := by
  have hv : CodesValue 21 = (11,8,10,7,1) := by rfl
  have hm : (11,8,10,7,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case22 : CodesAt 22 := by
  have hv : CodesValue 22 = (11,8,10,7,2) := by rfl
  have hm : (11,8,10,7,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case23 : CodesAt 23 := by
  have hv : CodesValue 23 = (11,8,10,7,3) := by rfl
  have hm : (11,8,10,7,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_singleton_self _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
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
lemma codes_interval01 : FiniteIntervals.Covers CodesIndex 16 24 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 16 8
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
lemma codes_valid : ∀ i : FiveWordOrbits3.Cases, ((FiveRows3.digit0 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit1 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit2 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit3 (FiveWordOrbits3.caseKey i).val).val + 1,(FiveRows3.digit4 (FiveWordOrbits3.caseKey i).val).val + 1) ∈ goodCodes := by
  intro i
  have hc : FiniteIntervals.Covers CodesIndex 0 24 := (FiniteIntervals.merge codes_interval00 codes_interval01)
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma codes_of_good (j : Fin 62208) (hj : j ∈ FiveRows3.good) :
    ((FiveRows3.digit0 j.val).val + 1,(FiveRows3.digit1 j.val).val + 1,(FiveRows3.digit2 j.val).val + 1,(FiveRows3.digit3 j.val).val + 1,(FiveRows3.digit4 j.val).val + 1) ∈ goodCodes := by
  rw [FiveWordOrbits3.good_eq] at hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact codes_valid i

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5)) := by
  have hs := SixProjection31.localBounds o h
  have hc := codes_of_good ⟨FiveRows3.key (smallOrders o),FiveRows3.key_lt (smallOrders o)⟩
    (SixProjection31.catalogue o h)
  rw [FiveRows3.digit_key0,FiveRows3.digit_key1,FiveRows3.digit_key2,FiveRows3.digit_key3,FiveRows3.digit_key4] at hc
  have hr0 := FiveRows3.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 2) hr0
  have hr1 := FiveRows3.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 3) hr1
  have hr2 := FiveRows3.chosen2 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr2
  have he2 := row2 (o 4) hr2
  have hr3 := FiveRows3.chosen3 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr3
  have he3 := row3 (o 5) hr3
  have hr4 := FiveRows3.chosen4 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr4
  have he4 := row4 (o 0) hr4
  unfold Compatible
  rw [he0,he1,he2,he3,he4]
  simpa only [smallOrders,Fin.cases_zero,Fin.cases_succ] using hc

#print axioms compatible
end Erdos184Work.SixProjectionCode31
