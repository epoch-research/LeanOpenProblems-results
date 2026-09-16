import Submission.Tree
import Submission.Data1

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_1_valid : check_list 10000 20000 chunk_data_1 = true := by decide
