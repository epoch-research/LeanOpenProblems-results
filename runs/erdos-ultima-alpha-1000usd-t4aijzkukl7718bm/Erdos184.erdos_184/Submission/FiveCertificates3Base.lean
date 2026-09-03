import Submission.FiveRows3
import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Case-indexed interface for finite five-color circuit certificates. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Cases := PureFiveFilter3.Cases
abbrev caseKey := PureFiveFilter3.caseKey
lemma caseKey_lt : ∀ i : Cases, caseKey i < 62208 := by decide +kernel

def good : Finset (Fin 62208) := {35235,35236,35237,35373,35374,35375,40851,40852,40853,40989,40990,40991,49530,49531,49532,49590,49591,49592,55146,55147,55148,55206,55207,55208}
def caseSource (i : Cases) : E → W := srcAt (digit0 (caseKey i)) (digit1 (caseKey i)) (digit2 (caseKey i)) (digit3 (caseKey i)) (digit4 (caseKey i))
def caseTarget (i : Cases) : E → W := dstAt (digit0 (caseKey i)) (digit1 (caseKey i)) (digit2 (caseKey i)) (digit3 (caseKey i)) (digit4 (caseKey i))
def Certificate (i : Cases) : Prop :=
  ∃ D : PartitionData E W,
    D.Valid (caseSource i) (caseTarget i) Finset.univ ∧
    (D.size ≤ 5 → D.size = 2 ∧ (⟨caseKey i,caseKey_lt i⟩ : Fin 62208) ∈ good)
def CertificateAt (j : ℕ) : Prop := ∀ hj : j < 3312, Certificate ⟨j,hj⟩
#print axioms caseKey_lt
end Erdos184Work.FiveRows3
