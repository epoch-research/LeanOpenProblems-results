import Submission.Tree
import Submission.Data92

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_92_valid : check_list 920000 930000 chunk_data_92 = true := by decide
