import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_6 : (records 6).all (checkCertificate (model 6)) = true := by
  decide +kernel

lemma configs_checked_6 : configs (model 6) = ((records 6).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
