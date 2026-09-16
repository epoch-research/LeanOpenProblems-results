import Submission.Tree
import Submission.Data23

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_23_valid : check_list 230000 240000 chunk_data_23 = true := by decide
