import Submission.Tree
import Submission.Data17

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_17_valid : check_list 170000 180000 chunk_data_17 = true := by decide
