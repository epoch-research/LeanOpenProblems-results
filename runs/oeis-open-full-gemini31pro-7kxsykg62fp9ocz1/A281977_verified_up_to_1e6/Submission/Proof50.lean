import Submission.Tree
import Submission.Data50

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_50_valid : check_list 500000 510000 chunk_data_50 = true := by decide
