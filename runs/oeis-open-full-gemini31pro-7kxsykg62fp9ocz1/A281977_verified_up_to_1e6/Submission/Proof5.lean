import Submission.Tree
import Submission.Data5

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_5_valid : check_list 50000 60000 chunk_data_5 = true := by decide
