import Submission.FiveCertificates2_000
import Submission.FiveCertificates2_001
import Submission.FiveCertificates2_002
import Submission.FiveCertificates2_003
import Submission.FiveCertificates2_004
import Submission.FiveCertificates2_005
import Submission.FiveCertificates2_006
import Submission.FiveCertificates2_007
import Submission.FiveCertificates2_008
import Submission.FiveCertificates2_009
import Submission.FiveCertificates2_010

/-! Assembly of the independently checked five-color certificates. -/
namespace Erdos184Work.FiveRows2
open LabelKernel Erdos184Serial
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_cover : FiniteIntervals.Covers CertificateAt 0 2052 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge certificateInterval0 certificateInterval1) (FiniteIntervals.merge certificateInterval2 (FiniteIntervals.merge certificateInterval3 certificateInterval4))) (FiniteIntervals.merge (FiniteIntervals.merge certificateInterval5 (FiniteIntervals.merge certificateInterval6 certificateInterval7)) (FiniteIntervals.merge certificateInterval8 (FiniteIntervals.merge certificateInterval9 certificateInterval10))))
lemma certificates (i : Cases) : Certificate i :=
  certificate_cover i.val (Nat.zero_le _) i.isLt i.isLt
noncomputable def data (i : Cases) : PartitionData E W := (certificates i).choose
lemma data_valid (i : Cases) :
    (data i).Valid (caseSource i) (caseTarget i) Finset.univ := (certificates i).choose_spec.1
lemma data_size (i : Cases) (h : (data i).size ≤ 5) :
    (data i).size = 2 ∧ (⟨caseKey i,caseKey_lt i⟩ : Fin 77760) ∈ good :=
  (certificates i).choose_spec.2 h
#print axioms certificates
#print axioms data_valid
#print axioms data_size
end Erdos184Work.FiveRows2
