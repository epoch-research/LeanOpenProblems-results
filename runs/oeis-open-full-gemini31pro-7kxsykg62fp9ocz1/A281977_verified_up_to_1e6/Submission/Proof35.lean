import Submission.Tree
import Submission.Data35

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_35_valid : check_list 350000 360000 chunk_data_35 = true := by decide
