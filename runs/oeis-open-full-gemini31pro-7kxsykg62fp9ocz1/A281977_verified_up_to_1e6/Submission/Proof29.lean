import Submission.Tree
import Submission.Data29

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_29_valid : check_list 290000 300000 chunk_data_29 = true := by decide
