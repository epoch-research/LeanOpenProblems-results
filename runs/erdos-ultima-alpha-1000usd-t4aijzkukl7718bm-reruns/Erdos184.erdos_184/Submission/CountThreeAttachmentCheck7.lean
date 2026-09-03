import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_7 : (records 7).all (checkCertificate (model 7)) = true := by
  decide +kernel

lemma configs_checked_7 : configs (model 7) = ((records 7).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
