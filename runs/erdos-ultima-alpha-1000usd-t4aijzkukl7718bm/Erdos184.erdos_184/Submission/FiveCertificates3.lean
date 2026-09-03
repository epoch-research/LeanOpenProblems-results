import Submission.FiveCertificates3_000
import Submission.FiveCertificates3_001
import Submission.FiveCertificates3_002
import Submission.FiveCertificates3_003
import Submission.FiveCertificates3_004
import Submission.FiveCertificates3_005
import Submission.FiveCertificates3_006
import Submission.FiveCertificates3_007
import Submission.FiveCertificates3_008
import Submission.FiveCertificates3_009
import Submission.FiveCertificates3_010
import Submission.FiveCertificates3_011
import Submission.FiveCertificates3_012
import Submission.FiveCertificates3_013
import Submission.FiveCertificates3_014
import Submission.FiveCertificates3_015
import Submission.FiveCertificates3_016

/-! Assembly of the independently checked five-color certificates. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_cover : FiniteIntervals.Covers CertificateAt 0 3312 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge certificateInterval0 certificateInterval1) (FiniteIntervals.merge certificateInterval2 certificateInterval3)) (FiniteIntervals.merge (FiniteIntervals.merge certificateInterval4 certificateInterval5) (FiniteIntervals.merge certificateInterval6 certificateInterval7))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge certificateInterval8 certificateInterval9) (FiniteIntervals.merge certificateInterval10 certificateInterval11)) (FiniteIntervals.merge (FiniteIntervals.merge certificateInterval12 certificateInterval13) (FiniteIntervals.merge certificateInterval14 (FiniteIntervals.merge certificateInterval15 certificateInterval16)))))
lemma certificates (i : Cases) : Certificate i :=
  certificate_cover i.val (Nat.zero_le _) i.isLt i.isLt
noncomputable def data (i : Cases) : PartitionData E W := (certificates i).choose
lemma data_valid (i : Cases) :
    (data i).Valid (caseSource i) (caseTarget i) Finset.univ := (certificates i).choose_spec.1
lemma data_size (i : Cases) (h : (data i).size ≤ 5) :
    (data i).size = 2 ∧ (⟨caseKey i,caseKey_lt i⟩ : Fin 62208) ∈ good :=
  (certificates i).choose_spec.2 h
#print axioms certificates
#print axioms data_valid
#print axioms data_size
end Erdos184Work.FiveRows3
