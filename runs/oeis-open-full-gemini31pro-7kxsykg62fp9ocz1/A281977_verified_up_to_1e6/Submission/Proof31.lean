import Submission.Tree
import Submission.Data31

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_31_valid : check_list 310000 320000 chunk_data_31 = true := by decide
