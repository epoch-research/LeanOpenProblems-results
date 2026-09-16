import Submission.Tree
import Submission.Data66

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_66_valid : check_list 660000 670000 chunk_data_66 = true := by decide
