import Submission.Tree
import Submission.Data67

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_67_valid : check_list 670000 680000 chunk_data_67 = true := by decide
