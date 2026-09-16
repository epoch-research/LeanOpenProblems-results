import Submission.Tree
import Submission.Data10

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_10_valid : check_list 100000 110000 chunk_data_10 = true := by decide
