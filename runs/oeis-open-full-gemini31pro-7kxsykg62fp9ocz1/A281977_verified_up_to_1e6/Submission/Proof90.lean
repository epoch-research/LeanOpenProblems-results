import Submission.Tree
import Submission.Data90

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_90_valid : check_list 900000 910000 chunk_data_90 = true := by decide
