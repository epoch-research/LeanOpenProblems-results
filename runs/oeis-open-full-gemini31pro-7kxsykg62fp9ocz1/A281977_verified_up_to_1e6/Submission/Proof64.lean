import Submission.Tree
import Submission.Data64

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_64_valid : check_list 640000 650000 chunk_data_64 = true := by decide
