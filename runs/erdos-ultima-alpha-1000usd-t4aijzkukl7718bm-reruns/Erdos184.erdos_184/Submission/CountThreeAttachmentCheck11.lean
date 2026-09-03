import Submission.CountThreeAttachmentBase

/-! Kernel verification of one finite attachment model. -/
namespace Erdos184.CountThreeAttachmentData
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

lemma certificates_checked_11 : (records 11).all (checkCertificate (model 11)) = true := by
  decide +kernel

lemma configs_checked_11 : configs (model 11) = ((records 11).toList.map (·.config)) := by
  decide +kernel

end Erdos184.CountThreeAttachmentData
