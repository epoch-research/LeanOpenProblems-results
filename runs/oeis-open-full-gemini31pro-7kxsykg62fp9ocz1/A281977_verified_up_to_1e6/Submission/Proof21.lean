import Submission.Tree
import Submission.Data21

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_21_valid : check_list 210000 220000 chunk_data_21 = true := by decide
