import Submission.CountThreeAttachmentCheck0
import Submission.CountThreeAttachmentCheck1
import Submission.CountThreeAttachmentCheck2
import Submission.CountThreeAttachmentCheck3
import Submission.CountThreeAttachmentCheck4
import Submission.CountThreeAttachmentCheck5
import Submission.CountThreeAttachmentCheck6
import Submission.CountThreeAttachmentCheck7
import Submission.CountThreeAttachmentCheck8
import Submission.CountThreeAttachmentCheck9
import Submission.CountThreeAttachmentCheck10
import Submission.CountThreeAttachmentCheck11

/-! Combined kernel-checked finite attachment certificates. -/
namespace Erdos184.CountThreeAttachmentData
lemma certificates_checked (i : Fin 12) :
    (records i).all (checkCertificate (model i)) = true := by
  fin_cases i
  · exact certificates_checked_0
  · exact certificates_checked_1
  · exact certificates_checked_2
  · exact certificates_checked_3
  · exact certificates_checked_4
  · exact certificates_checked_5
  · exact certificates_checked_6
  · exact certificates_checked_7
  · exact certificates_checked_8
  · exact certificates_checked_9
  · exact certificates_checked_10
  · exact certificates_checked_11

lemma configs_checked (i : Fin 12) :
    configs (model i) = ((records i).toList.map (·.config)) := by
  fin_cases i
  · exact configs_checked_0
  · exact configs_checked_1
  · exact configs_checked_2
  · exact configs_checked_3
  · exact configs_checked_4
  · exact configs_checked_5
  · exact configs_checked_6
  · exact configs_checked_7
  · exact configs_checked_8
  · exact configs_checked_9
  · exact configs_checked_10
  · exact configs_checked_11

end Erdos184.CountThreeAttachmentData
