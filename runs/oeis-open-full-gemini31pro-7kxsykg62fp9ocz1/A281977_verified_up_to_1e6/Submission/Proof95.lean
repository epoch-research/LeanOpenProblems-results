import Submission.Tree
import Submission.Data95

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_95_valid : check_list 950000 960000 chunk_data_95 = true := by decide
