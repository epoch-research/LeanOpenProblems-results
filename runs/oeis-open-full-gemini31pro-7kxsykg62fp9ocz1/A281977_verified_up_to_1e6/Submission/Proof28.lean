import Submission.Tree
import Submission.Data28

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_28_valid : check_list 280000 290000 chunk_data_28 = true := by decide
