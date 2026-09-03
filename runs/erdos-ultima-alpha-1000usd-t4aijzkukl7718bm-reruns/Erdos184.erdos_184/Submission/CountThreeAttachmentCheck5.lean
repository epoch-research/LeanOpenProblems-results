import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_5 : (records 5).all (checkCertificate (model 5)) = true := by
  decide +kernel

lemma configs_checked_5 : configs (model 5) = ((records 5).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
