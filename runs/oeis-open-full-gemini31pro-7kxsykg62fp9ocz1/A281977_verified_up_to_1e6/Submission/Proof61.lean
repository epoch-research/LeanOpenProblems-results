import Submission.Tree
import Submission.Data61

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_61_valid : check_list 610000 620000 chunk_data_61 = true := by decide
