import Submission.Tree
import Submission.Data16

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_16_valid : check_list 160000 170000 chunk_data_16 = true := by decide
