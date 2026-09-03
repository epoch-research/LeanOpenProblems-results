import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block719 : Table.Every Certificate block719 := by decide +kernel
lemma good_block719 : Table.Every GoodCertificate block719 := by decide +kernel
#print axioms certificate_block719
end Erdos184Work.PureSixOrbitLookup0
