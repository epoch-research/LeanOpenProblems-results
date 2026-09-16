import Submission.Tree
import Submission.Data75

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_75_valid : check_list 750000 760000 chunk_data_75 = true := by decide
