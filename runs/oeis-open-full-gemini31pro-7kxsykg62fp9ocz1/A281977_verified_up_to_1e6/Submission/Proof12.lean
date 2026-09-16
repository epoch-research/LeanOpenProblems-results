import Submission.Tree
import Submission.Data12

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_12_valid : check_list 120000 130000 chunk_data_12 = true := by decide
