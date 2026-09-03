import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block891 : Table.Every Certificate block891 := by decide +kernel
lemma good_block891 : Table.Every GoodCertificate block891 := by decide +kernel
#print axioms certificate_block891
end Erdos184Work.PureSixOrbitLookup0
