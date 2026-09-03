import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_10 : (records 10).all (checkCertificate (model 10)) = true := by
  decide +kernel

lemma configs_checked_10 : configs (model 10) = ((records 10).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
