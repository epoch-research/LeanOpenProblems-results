import Submission.Tree
import Submission.Data7

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_7_valid : check_list 70000 80000 chunk_data_7 = true := by decide
