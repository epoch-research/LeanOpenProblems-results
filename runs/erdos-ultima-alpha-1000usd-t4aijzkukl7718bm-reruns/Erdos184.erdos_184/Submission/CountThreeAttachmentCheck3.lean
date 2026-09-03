import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_3 : (records 3).all (checkCertificate (model 3)) = true := by
  decide +kernel

lemma configs_checked_3 : configs (model 3) = ((records 3).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
