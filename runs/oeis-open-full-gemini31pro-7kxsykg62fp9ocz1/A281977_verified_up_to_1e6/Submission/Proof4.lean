import Submission.Tree
import Submission.Data4

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_4_valid : check_list 40000 50000 chunk_data_4 = true := by decide
