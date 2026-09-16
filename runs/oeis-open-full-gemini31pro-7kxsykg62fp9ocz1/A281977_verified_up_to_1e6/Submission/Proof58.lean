import Submission.Tree
import Submission.Data58

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_58_valid : check_list 580000 590000 chunk_data_58 = true := by decide
