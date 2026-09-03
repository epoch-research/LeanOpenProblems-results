import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_4 : (records 4).all (checkCertificate (model 4)) = true := by
  decide +kernel

lemma configs_checked_4 : configs (model 4) = ((records 4).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
