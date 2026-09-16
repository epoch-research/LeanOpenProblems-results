import Submission.Tree
import Submission.Data87

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_87_valid : check_list 870000 880000 chunk_data_87 = true := by decide
