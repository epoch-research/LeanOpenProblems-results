import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block267 : Table.Every Certificate block267 := by decide +kernel
lemma good_block267 : Table.Every GoodCertificate block267 := by decide +kernel
#print axioms certificate_block267
end Erdos184Work.PureSixOrbitLookup0
