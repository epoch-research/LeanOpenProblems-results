import Submission.Tree
import Submission.Data13

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_13_valid : check_list 130000 140000 chunk_data_13 = true := by decide
