import Submission.Tree
import Submission.Data9

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_9_valid : check_list 90000 100000 chunk_data_9 = true := by decide
