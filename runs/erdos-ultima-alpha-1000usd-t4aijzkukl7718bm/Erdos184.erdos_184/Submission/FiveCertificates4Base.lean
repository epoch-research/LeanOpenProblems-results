import Submission.FiveRows4
import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Case-indexed interface for finite five-color circuit certificates. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Cases := PureFiveFilter4.Cases
abbrev caseKey := PureFiveFilter4.caseKey
lemma caseKey_lt : ∀ i : Cases, caseKey i < 1244160 := by decide +kernel

def good : Finset (Fin 1244160) := ∅
def caseSource (i : Cases) : E → W := srcAt (digit0 (caseKey i)) (digit1 (caseKey i)) (digit2 (caseKey i)) (digit3 (caseKey i)) (digit4 (caseKey i))
def caseTarget (i : Cases) : E → W := dstAt (digit0 (caseKey i)) (digit1 (caseKey i)) (digit2 (caseKey i)) (digit3 (caseKey i)) (digit4 (caseKey i))
def Certificate (i : Cases) : Prop :=
  ∃ D : PartitionData E W,
    D.Valid (caseSource i) (caseTarget i) Finset.univ ∧
    (D.size ≤ 5 → D.size = 2 ∧ (⟨caseKey i,caseKey_lt i⟩ : Fin 1244160) ∈ good)
def CertificateAt (j : ℕ) : Prop := ∀ hj : j < 760, Certificate ⟨j,hj⟩
#print axioms caseKey_lt
end Erdos184Work.FiveRows4
