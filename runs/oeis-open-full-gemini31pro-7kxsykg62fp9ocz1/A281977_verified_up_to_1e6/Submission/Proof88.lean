import Submission.Tree
import Submission.Data88

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_88_valid : check_list 880000 890000 chunk_data_88 = true := by decide
