import Submission.Tree
import Submission.Data15

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_15_valid : check_list 150000 160000 chunk_data_15 = true := by decide
