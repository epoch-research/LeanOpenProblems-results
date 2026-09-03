import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block19 : Table.Every Certificate block19 := by decide +kernel
lemma good_block19 : Table.Every GoodCertificate block19 := by decide +kernel
#print axioms certificate_block19
end Erdos184Work.PureSixOrbitLookup0
