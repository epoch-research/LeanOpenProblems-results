import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_9 : (records 9).all (checkCertificate (model 9)) = true := by
  decide +kernel

lemma configs_checked_9 : configs (model 9) = ((records 9).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
