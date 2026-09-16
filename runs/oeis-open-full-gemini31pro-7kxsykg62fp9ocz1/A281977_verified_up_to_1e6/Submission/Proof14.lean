import Submission.Tree
import Submission.Data14

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_14_valid : check_list 140000 150000 chunk_data_14 = true := by decide
