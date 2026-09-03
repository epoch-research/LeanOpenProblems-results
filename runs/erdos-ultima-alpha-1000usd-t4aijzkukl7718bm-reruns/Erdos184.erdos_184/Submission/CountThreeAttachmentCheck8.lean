import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_8 : (records 8).all (checkCertificate (model 8)) = true := by
  decide +kernel

lemma configs_checked_8 : configs (model 8) = ((records 8).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
