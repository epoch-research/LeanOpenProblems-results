import Submission.Tree
import Submission.Data22

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_22_valid : check_list 220000 230000 chunk_data_22 = true := by decide
