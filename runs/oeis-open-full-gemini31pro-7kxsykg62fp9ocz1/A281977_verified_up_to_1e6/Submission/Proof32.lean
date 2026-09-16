import Submission.Tree
import Submission.Data32

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_32_valid : check_list 320000 330000 chunk_data_32 = true := by decide
