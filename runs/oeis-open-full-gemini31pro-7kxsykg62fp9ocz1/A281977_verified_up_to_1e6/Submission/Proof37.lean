import Submission.Tree
import Submission.Data37

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_37_valid : check_list 370000 380000 chunk_data_37 = true := by decide
