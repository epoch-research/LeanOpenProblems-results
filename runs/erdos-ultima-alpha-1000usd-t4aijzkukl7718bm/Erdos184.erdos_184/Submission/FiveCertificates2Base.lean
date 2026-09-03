import Submission.FiveRows2
import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Case-indexed interface for finite five-color circuit certificates. -/
namespace Erdos184Work.FiveRows2
open LabelKernel Erdos184Serial
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Cases := PureFiveFilter2.Cases
abbrev caseKey := PureFiveFilter2.caseKey
lemma caseKey_lt : ∀ i : Cases, caseKey i < 77760 := by decide +kernel

def good : Finset (Fin 77760) := {32176,32179,32180,33357,33358,33361,34674,34676,34895,34901,36273,36274,36277,37163,37169,37374,37376,38764,38767,38768,44555,44557,44558,44838,44839,44841,45450,45452,45540,45546,49105,49108,49109,49532,49534,49535,49932,49933,49935,50625,50627,50751,50757,54408,54409,54412,55477,55480,55481,56676,56677,56680,58047,58049,58241,58247,59213,59219,59451,59453,65300,65302,65303,65592,65593,65595,67667,67669,67670,68058,68059,68061,72972,72978,73206,73208,75591,75597,75789,75791}
def caseSource (i : Cases) : E → W := srcAt (digit0 (caseKey i)) (digit1 (caseKey i)) (digit2 (caseKey i)) (digit3 (caseKey i)) (digit4 (caseKey i))
def caseTarget (i : Cases) : E → W := dstAt (digit0 (caseKey i)) (digit1 (caseKey i)) (digit2 (caseKey i)) (digit3 (caseKey i)) (digit4 (caseKey i))
def Certificate (i : Cases) : Prop :=
  ∃ D : PartitionData E W,
    D.Valid (caseSource i) (caseTarget i) Finset.univ ∧
    (D.size ≤ 5 → D.size = 2 ∧ (⟨caseKey i,caseKey_lt i⟩ : Fin 77760) ∈ good)
def CertificateAt (j : ℕ) : Prop := ∀ hj : j < 2052, Certificate ⟨j,hj⟩
#print axioms caseKey_lt
end Erdos184Work.FiveRows2
