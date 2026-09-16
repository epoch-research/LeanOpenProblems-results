import Submission.Tree
import Submission.Data70

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_70_valid : check_list 700000 710000 chunk_data_70 = true := by decide
