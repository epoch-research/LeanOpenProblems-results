import Submission.Tree
import Submission.Data84

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_84_valid : check_list 840000 850000 chunk_data_84 = true := by decide
