import Submission.Tree
import Submission.Data26

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_26_valid : check_list 260000 270000 chunk_data_26 = true := by decide
