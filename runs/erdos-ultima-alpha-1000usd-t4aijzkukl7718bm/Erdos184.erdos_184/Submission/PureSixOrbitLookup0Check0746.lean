import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block746 : Table.Every Certificate block746 := by decide +kernel
lemma good_block746 : Table.Every GoodCertificate block746 := by decide +kernel
#print axioms certificate_block746
end Erdos184Work.PureSixOrbitLookup0
