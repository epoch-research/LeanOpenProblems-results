import Submission.Tree
import Submission.Data57

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_57_valid : check_list 570000 580000 chunk_data_57 = true := by decide
