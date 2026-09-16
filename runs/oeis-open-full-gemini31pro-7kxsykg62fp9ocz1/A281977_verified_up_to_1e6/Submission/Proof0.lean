import Submission.Tree
import Submission.Data0

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_0_valid : check_list 0 10000 chunk_data_0 = true := by decide
